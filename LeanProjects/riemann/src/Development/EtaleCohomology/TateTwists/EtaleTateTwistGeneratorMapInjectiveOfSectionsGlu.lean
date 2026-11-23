import Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapIsIsoOfInjSurj
import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosure
import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsSeparatedAndGlue
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem ulift_smul_eq {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (x : M) : r • x = r.down.val • x := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    apply ULift.ext; simp only [ULift.down_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  rw [Nat.cast_smul_eq_nsmul]

theorem q_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (c : ℕ) (hc : q ∣ c) (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simpa using (ZMod.natCast_eq_zero_iff c q).2 hc
  rw [this, zero_smul]

theorem exists_functional {q : ℕ} [NeZero q] {M : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (g : M) (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) :
    ∃ F : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), F g = 1 := by
  letI : Module (ZMod q) M :=
    Module.compHom M (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom
  have hsm : ∀ (r : ZMod q) (x : M), r • x = (ULift.up r : ULift.{1} (ZMod q)) • x := fun r x => rfl
  let f : ZMod q →ₗ[ZMod q] M := LinearMap.toSpanSingleton (ZMod q) M g
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : r.val • g = 0 := by
      have h2 : (ULift.up r : ULift.{1} (ZMod q)) • g = 0 := hr
      have h4 := ulift_smul_eq (M := M) (ULift.up r : ULift.{1} (ZMod q)) g
      exact h4.symm.trans h2
    have h3 := hg _ h1
    rw [← ZMod.natCast_zmod_val r]
    exact (ZMod.natCast_eq_zero_iff _ _).2 h3
  obtain ⟨h, hh⟩ := (KStar.Selmer.zmod_baer (N := q)).extension_property f hf LinearMap.id
  refine ⟨{ toFun := fun x => ULift.up (h x), map_add' := fun x y => by ext; simp,
             map_smul' := fun r x => ?_ }, ?_⟩
  · change ULift.up (h (r.down • x)) = r • ULift.up (h x)
    rw [h.map_smul]
    ext; simp [smul_eq_mul]
  · have := LinearMap.congr_fun hh 1
    simp only [LinearMap.comp_apply, f, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply] at this
    ext; simpa using this

theorem dvd_of_tmul {q : ℕ} [NeZero q] {M N : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N] (g : M) (g' : N)
    (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) (hg' : ∀ c : ℕ, c • g' = 0 → q ∣ c) (c : ℕ)
    (h : c • (g ⊗ₜ[ULift.{1} (ZMod q)] g') = 0) : q ∣ c := by
  obtain ⟨F, hF⟩ := exists_functional g hg
  obtain ⟨F', hF'⟩ := exists_functional g' hg'
  let L := TensorProduct.lift ((LinearMap.mul (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))).compl₂ F' ∘ₗ F)
  have := congrArg L h
  simp only [map_nsmul, L, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.mul_apply', hF, hF', mul_one, map_zero, nsmul_eq_mul] at this
  have h2 := congrArg ULift.down this
  simp at h2
  exact (ZMod.natCast_eq_zero_iff _ _).1 h2

end LateralTheory.EtaleFoundations.GenIsoInj

namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem sm_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := map_nsmul _ _ _
theorem sm_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sr_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _
theorem sr_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sgl_smul_eq_zero {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (c : ℕ) (x : Sec F U)
    (h : c • Sec.map (sglι F) x = 0) : c • x = 0 := by
  let ψ : (sgl F).X 0 ⟶ F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
  have hψ : sglι F ≫ ψ = 𝟙 F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  have e : ∀ y : Sec F U, Sec.map ψ (Sec.map (sglι F) y) = y := fun y => by
    rw [TwMulPf.sec_map_comp, hψ, TwMulPf.sec_map_id]
  have h' : Sec.map (sglι F) (c • x) = Sec.map (sglι F) 0 := by
    rw [show Sec.map (sglι F) (c • x) = c • Sec.map (sglι F) x from map_nsmul _ c x, h]
    exact (map_zero _).symm
  have := congrArg (Sec.map ψ) h'
  rwa [e, e] at this

end LateralTheory.EtaleFoundations.GenIsoInj

open LateralTheory.EtaleFoundations.GenIsoInj LateralTheory.EtaleFoundations.TwMulPf in

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_injective_of_sections_glue (hts : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (hlb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (hsg : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective := by
  classical
  intro q _ i j k T μ hμ hk φ hφ U a ha
  have nt : ∀ (l : ℤ) (W : Scheme.{0}) [Nonempty W] (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
      c • Sec.map (sglι (tw q l)) (twGen l ζ) = 0 → q ∣ c :=
    fun l W _ ζ c h => (hts q l).2.2.1 W ζ c (sgl_smul_eq_zero c _ h)
  refine hlb.2.2.2.2.1 U _ (hlb.2.1 U _ _ ((hts q k).1 U a) ?_)
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact hlb.1 V _ fun W h => by rw [res_comp, h0, sr_zero]
  · have h1 : c • μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ))
        (Sec.map (sglι _) (twGen j ζ)) = 0 := by
      rw [← hφ V ζ, ← sm_nsmul, ← sm_nsmul, ← hc, ← sec_res_map, ha, sr_zero, sm_zero]
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V)
        ⟨(0, 0), rfl⟩ (c • (Sec.map (sglι _) (twGen i ζ) ⊗ₜ Sec.map (sglι _) (twGen j ζ)))
    have hx : μ.lift V 0 x = 0 := by
      simp only [x, Pair.lift, DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]
      exact h1
    refine hlb.2.1 V _ _ (hμ.2 V 0 x hx) fun W h hW => ?_
    have hW' : c • (Sec.res h (Sec.map (sglι _) (twGen i ζ)) ⊗ₜ[ULift.{1} (ZMod q)]
        Sec.res h (Sec.map (sglι _) (twGen j ζ))) = 0 := by
      have := congrArg (DirectSum.component (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) W ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) W)
        ⟨(0, 0), rfl⟩) hW
      simpa [x, Tens.res, DirectSum.component.lof_self] using this
    show Sec.res (h ≫ g) a = 0
    rw [res_comp, hc, sr_nsmul]
    by_cases hne : Nonempty W
    · rw [sec_res_map, sec_res_map, (hts q i).2.2.2.1, (hts q j).2.2.2.1] at hW'
      exact q_smul c (dvd_of_tmul _ _ (nt i W _) (nt j W _) c hW') _
    · have : IsEmpty W := not_nonempty_iff.1 hne
      exact (hsg (ZMod q) (tw q k) W).1 _ _ (hlb.2.2.2.2.2.2 W _)
