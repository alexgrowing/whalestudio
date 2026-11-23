import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulInj

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose R hR hRQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h V g (hSP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => hR V g hg)
  · rintro W _ ⟨V, k, g, hg, hk, rfl⟩
    exact hRQ V g hg W k hk

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_empty {U : Scheme.{0}} [IsEmpty U] {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology (P := @Etale) U, fun _ _ hg => hg.elim⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem sglι_left {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom (Sec.map (sglι F) x) = x := by
  have h := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  exact (congrArg (fun f : F ⟶ F => (f.hom.app (op U)).hom x) h).trans rfl

theorem nsmul_eq_zero_of_dvd {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {c : ℕ} (h : q ∣ c)
    (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp only [ULift.down_natCast, ULift.zero_down]
    exact (CharP.cast_eq_zero_iff (ZMod q) q c).2 h
  rw [this, zero_smul]

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res (F := F) g 0 = 0 :=
  map_zero _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x :=
  map_nsmul _ _ _

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul _ _ _

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj
variable {R : Type} [CommRing R]

theorem tmap_nsmul {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) M'] [Module (ULift.{1} R) N']
    (f : M →ₗ[ULift.{1} R] M') (g : N →ₗ[ULift.{1} R] N') (c : ℕ) (s : M) (t : N) :
    TensorProduct.map f g (c • (s ⊗ₜ[ULift.{1} R] t)) = c • (f s ⊗ₜ g t) := by
  rw [map_nsmul, TensorProduct.map_tmul]

theorem tens_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (c • (Sec.res g s ⊗ₜ Sec.res g t)) := by
  classical
  unfold Tens.res
  rw [DirectSum.lmap_lof, tmap_nsmul]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) = c • μ.mul U p.1.1 p.1.2 w p.2 s t := by
  classical
  unfold Pair.lift
  rw [DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]

theorem lof_eq_zero {ι : Type*} [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module (ULift.{1} R) (M i)]
    (i : ι) (x : M i) (h : DirectSum.lof (ULift.{1} R) ι M i x = 0) : x = 0 :=
  DirectSum.of_injective (β := M) i (h.trans (map_zero _).symm)

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj

theorem tw_mul_loc_injective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → (∀ (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c) → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  intro q _ i j k hk hyp K τ hτ φ hφ U a ha
  have Tk := GlobalTheory.T.tateTwist_sections_locally_generated q k
  have Ti := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have Tj := GlobalTheory.T.tateTwist_sections_locally_generated q j
  refine loc_bind (Tk.1 U a) ?_
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact loc_top fun W k' => by rw [res_comp, h0, res_zero]
  ·
    have hres : ∀ (W : Scheme.{0}) (h : W ⟶ V), Sec.res (h ≫ g) a = c • Sec.res h (twGen k ζ) := by
      intro W h
      rw [res_comp, hc, res_nsmul]
    set A := Sec.map (sglι (tw q i)) (twGen i ζ) with hA
    set B := Sec.map (sglι (tw q j)) (twGen j ζ) with hB
    have h1 : c • τ.mul V 0 0 0 (add_zero 0) A B = 0 := by
      rw [← hφ V ζ, ← map_nsmul', ← hc, map_res, ha, res_zero]
    classical
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = 0} =>
        Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V) ⟨(0, 0), by simp⟩ (c • (A ⊗ₜ B))
    have hx : τ.lift V 0 x = 0 := (lift_lof τ V 0 ⟨(0, 0), by simp⟩ A B c).trans h1
    refine loc_bind (hτ.2 V 0 x hx) ?_
    intro V' g' hx'

    set ζ' := ζ.map g'.appTop.hom with hζ'
    have h2 : c • (twGen i ζ' ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ') = 0 := by
      have e2 := lof_eq_zero _ _ _ ((tens_res_lof g' 0 ⟨(0, 0), by simp⟩ A B c).symm.trans hx')
      have e3 : c • (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) ⊗ₜ[ULift.{1} (ZMod q)]
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom (Sec.res g' B)) = 0 :=
        (tmap_nsmul _ _ c _ _).symm.trans ((congrArg (TensorProduct.map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom) e2).trans (map_zero _))
      have ei : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) = twGen i ζ' := by
        have h := (map_res (sglι (tw q i)) g' (twGen i ζ)).symm
        rw [Ti.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      have ej : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom
          (Sec.res g' B) = twGen j ζ' := by
        have h := (map_res (sglι (tw q j)) g' (twGen j ζ)).symm
        rw [Tj.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      rw [ei, ej] at e3
      exact e3
    refine loc_bind (hyp V' ζ' c h2) ?_
    intro V'' g'' hq
    rcases isEmpty_or_nonempty V'' with hV | hV
    · exact loc_empty
    · have hqc := hq hV
      exact loc_top fun W h => by
        rw [hres, nsmul_eq_zero_of_dvd hqc]

end GlobalTheory.EtC.TwMulInj
