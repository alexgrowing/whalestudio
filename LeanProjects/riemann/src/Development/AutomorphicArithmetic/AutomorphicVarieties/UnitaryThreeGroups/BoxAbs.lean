import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GLiftToLiftInHAndSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg Topology

variable {O : Type} [CommRing O] [IsLocalRing O]

section Tools

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}
  {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
  [CommRing R''] [Algebra O R''] [IsCO O R'']

private theorem toLift_map (hη : IsLocallyConstant η) (r : GLift O η Ψ R) (f : R →ₐ[O] R') :
    (r.map f).toLift hη = (r.toLift hη).map f :=
  Lift.ext (MonoidHom.ext fun g => emb_map' (f : R →+* R') (r.hom g))

private theorem toLift_inj (hη : IsLocallyConstant η) {r r' : GLift O η Ψ R} (h : r.toLift hη = r'.toLift hη) :
    r = r' :=
  GLift.ext (MonoidHom.ext fun g => eq_of_emb ((r.hasMult g).trans (r'.hasMult g).symm)
    (DFunLike.congr_fun (congrArg Lift.hom h) g))

private theorem descend {G : Type} [Group G] [TopologicalSpace G] (π : G →* Γ) (hq : IsQuotientMap π)
    (r : GLift O (η.comp π) (Ψ.comp π) R) (h : π.ker ≤ r.hom.ker) :
    ∃ r' : GLift O η Ψ R, r'.comap π hq.continuous = r := by
  have hs := hq.surjective
  let φ := π.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨r.hom, h⟩
  have hφ : ∀ g, φ (π g) = r.hom g := fun g => π.liftOfRightInverse_comp_apply _ _ _ g
  refine ⟨⟨φ, fun a b n s => ?_, fun g => ?_⟩, GLift.ext (MonoidHom.ext hφ)⟩
  · rw [← hq.isOpen_preimage]
    have := r.cont a b n s
    simp only [← hφ] at this
    exact this
  · obtain ⟨g, rfl⟩ := hs g
    rw [hφ]
    exact r.red g

private theorem ker_closed (hη : IsLocallyConstant η) (r : GLift O η Ψ R) : IsClosed (r.hom.ker : Set Γ) := by
  have : (r.hom.ker : Set Γ) = ⋂ n : ℕ, {g | GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (r.hom g) = 1} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun h n => by rw [h, map_one], fun h => ?_⟩
    refine SemidirectProduct.ext (Units.ext ?_) (congrArg SemidirectProduct.right (h 0) :)
    ext a b
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := maximalIdeal R) inferInstance _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
    have := congrArg (fun x : GG 3 _ => x.mat a b) ((h n).trans (map_one (GG.map (Ideal.Quotient.mk _))).symm)
    exact this
  rw [this]
  exact isClosed_iInter fun n => (r.locConst hη n).isClosed_fiber 1

end Tools

theorem boxPres_abs (hP : LemmaP) (l : ℕ) [Fact l.Prime] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] [CharP (ResidueField O) l] (hl : l ≠ 2) {G Γ H : Type} [Group G] [TopologicalSpace G]
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
    [Group H] [TopologicalSpace H] (π : G →* Γ) (hq : IsQuotientMap π) (hΦ : PhiCond Γ l) {η : Γ →* ℤˣ}
    {Ψ : Γ →* Oˣ} (hη : IsLocallyConstant η) (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O))
    {Kill : Set G} {ι : H →* G} (hι : Continuous ι) {Q : Type} [Fintype Q] (D N : Q → Subgroup G)
    (hND : ∀ q, N q ≤ D q)
    (hK : ∀ (M : Subgroup G) [M.Normal], IsClosed (M : Set G) → ((∀ g ∈ Kill, g ∈ M) ↔ π.ker ≤ M ∧ ∀ q, N q ≤ M))
    (hN : ∀ q, ∀ n ∈ N q, r0 η Ψ (π n) = 1)
    (hloc : ∀ q, (form6 O).IsLocCond ((emb.comp (r0 η Ψ)).comp (π.comp (D q).subtype)) ((N q).subgroupOf (D q))
      (killCond ((emb.comp (rbar O η Ψ)).comp (π.comp (D q).subtype)) ((N q).subgroupOf (D q))))
    (hc : ∀ j, Module.Finite (ResidueField O) ((unitFrame π hq.continuous ι hι D N).Ob (adBar O η Ψ j)) ∧
      Module.finrank (ResidueField O) ((unitFrame π hq.continuous ι hι D N).Ob (adBar O η Ψ j)) =
        Module.finrank (ResidueField O) ((unitFrame π hq.continuous ι hι D N).H1c (adBar O η Ψ j)) + boxDef j)
    (U : Univ (GCond.noCondition O ((η.comp π).comp ι) ((Ψ.comp π).comp ι))) (I : Ideal U.R)
    (B : Univ (BoxCond Kill ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) (hW : IsLocPres U I WB) : BoxPres B WB := by
  have hπ := hq.continuous
  have hηG : IsLocallyConstant (η.comp π) := hη.comp_continuous hπ
  have hηH : IsLocallyConstant ((η.comp π).comp ι) := hηG.comp_continuous hι
  obtain ⟨hBK, f₀, hf₀, hI⟩ : BoxCond Kill ι hι U I B.R B.r := (B.rep B.R).1 (AlgHom.id O _)
  have hne : I ≠ ⊤ := fun h => RingHom.ker_ne_top f₀ (top_le_iff.1 (h ▸ hI))
  haveI : Nontrivial (U.R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (U.R ⧸ I) :=
    co_quot O U.R (U.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  let F := unitFrame π hπ ι hι D N
  let u := U.r.map (Ideal.Quotient.mkₐ O I)
  let ρ : ∀ v, Lift O ((emb.comp (rbar O η Ψ)).comp (F.φ v)) (U.R ⧸ I) := fun _ => u.toLift hηH
  obtain ⟨R, _, _, _, i, r, α, W, τ, κ, _, _, e, f, wf, ⟨⟨h1, h2, -, h4, h5⟩, hu⟩, hrel, hhom, -, hz, hτ, hκ⟩ :=
    hP l O hl _ ℤ wt6 (form6 O) Γ hΦ _ ((baseLift O η Ψ hΨ).toLift hη) (blockPairingForm_normalises_baseLift O η (barChar O Ψ))
      (blockPairingForm_normalises_baseLift O η Ψ) F (fun q => killCond _ (F.N q))
      (fun q n hn => by
        show emb (rbar O η Ψ (π n)) = 1
        rw [← baseLift_map_residue, hN q n hn, map_one, map_one])
      hloc (fun q n hn => by
        show emb (r0 η Ψ (π n)) = 1
        rw [hN q n hn, map_one])
      (fun j => (hc j).1) (U.R ⧸ I) WB ρ
      (fun s => by
        obtain ⟨g, a, b, -, h⟩ := hW.1 s
        have h1 : res O _ (emb (u.hom g) a b) = emb (rbar O _ _ g) a b := (u.toLift hηH).red g a b
        rw [← baseLift_map_residue, emb_map'] at h1
        rw [h, ← res_eq_zero_iff O, map_sub, AlgHom.commutes, sub_eq_zero]
        exact h1)
      (fun _ => (UpperTheory.gLift_toLift_inH_and_surjective hηH).1 u) (fun _ => hW.2)
  have hα : α = fun _ => 1 := funext fun _ => h4
  subst hα
  obtain ⟨r', rfl⟩ := (UpperTheory.gLift_toLift_inH_and_surjective hη).2 r h1
  have hloc' : U.r.map (i.comp (Ideal.Quotient.mkₐ O I)) = (r'.comap π hπ).comap ι hι := by
    refine toLift_inj hηH (Lift.ext (MonoidHom.ext fun s => ?_))
    have := h5 () s
    rw [mul_one, one_mul] at this
    exact (emb_map' (i : (U.R ⧸ I) →+* R) (u.hom s)).trans this.symm
  have hbox : BoxCond Kill ι hι U I R (r'.comap π hπ) := by
    refine ⟨(hK _ (ker_closed hηG (r'.comap π hπ))).2 ⟨fun g hg => ?_, fun q n hn => ?_⟩, _, hloc', fun y hy => ?_⟩
    · show r'.hom (π g) = 1
      rw [show π g = 1 from hg, map_one]
    · have h6 : emb (r'.hom (π n)) = 1 := h2 q ⟨n, hND q hn⟩ hn
      refine eq_of_emb ((r'.hasMult _).trans (congrArg SemidirectProduct.right (hN q n hn))) (h6.trans (map_one _).symm)
    · show i (Ideal.Quotient.mk I y) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
  obtain ⟨a, ha, -⟩ := (B.rep R).2 _ hbox
  obtain ⟨hB1, hB2⟩ := (hK _ (ker_closed hηG B.r)).1 hBK
  obtain ⟨r'', hr''⟩ := descend π hq B.r hB1
  have hr2 : ∀ g, r''.hom (π g) = B.r.hom g := fun g => DFunLike.congr_fun (congrArg GLift.hom hr'') g
  let i' : (U.R ⧸ I) →ₐ[O] B.R := Ideal.Quotient.liftₐ I f₀ hI
  have hi' : i'.comp (Ideal.Quotient.mkₐ O I) = f₀ := AlgHom.ext fun _ => rfl
  have hpush : push f₀ U.r.hom = B.r.hom.comp ι := congrArg GLift.hom hf₀
  obtain ⟨b, ⟨hb1, hb2, -⟩, -⟩ := hu B.R i' (r''.toLift hη) (fun _ => 1)
    ⟨(UpperTheory.gLift_toLift_inH_and_surjective hη).1 r'', fun q n hn => by
        show emb (r''.hom (π n)) = 1
        rw [hr2, show B.r.hom n = 1 from hB2 q hn, map_one],
      fun _ => (hh_group O _ ℤ wt6 (form6 O) B.R).1, rfl, fun _ s => by
        rw [mul_one, one_mul]
        refine Eq.trans ?_ (emb_map' (i' : (U.R ⧸ I) →+* B.R) (u.hom s))
        show emb (r''.hom (π (ι s))) = emb (push f₀ U.r.hom s)
        rw [hr2, hpush]
        rfl⟩
  have hb3 : r'.map b = r'' := toLift_inj hη ((toLift_map hη r' b).trans hb2)
  have hba : b.comp a = AlgHom.id O _ := by
    refine ((B.rep B.R).2 B.r ⟨hBK, f₀, hf₀, hI⟩).unique ?_ rfl
    calc B.r.map (b.comp a) = (B.r.map a).map b := rfl
      _ = (r'.map b).comap π hπ := by rw [ha]; rfl
      _ = B.r := by rw [hb3, hr'']
  have ha2 : r''.map a = r' := by
    refine GLift.ext (MonoidHom.ext fun g => ?_)
    obtain ⟨g, rfl⟩ := hq.surjective g
    show GG.map _ (r''.hom (π g)) = _
    rw [hr2]
    exact DFunLike.congr_fun (congrArg GLift.hom ha) g
  have hab : a.comp b = AlgHom.id O _ := by
    refine (hu R i (r'.toLift hη) (fun _ => 1) ⟨h1, h2, fun _ => (hh_group O _ ℤ wt6 (form6 O) R).1, rfl, h5⟩).unique
      ⟨?_, ?_, fun _ => Matrix.map_one _ (map_zero _) (map_one _)⟩ ⟨rfl, rfl, fun _ => Matrix.map_one _ rfl rfl⟩
    · rw [AlgHom.comp_assoc, hb1]
      refine Ideal.Quotient.algHom_ext O (((U.rep R).2 _ trivial).unique ?_ hloc')
      rw [AlgHom.comp_assoc, hi', ← ha]
      calc U.r.map (a.comp f₀) = (U.r.map f₀).map a := rfl
        _ = _ := by rw [hf₀]; rfl
    · rw [← toLift_map]
      congr 1
      calc r'.map (a.comp b) = (r'.map b).map a := rfl
        _ = r' := by rw [hb3, ha2]
  have hbs : Function.Surjective b := fun y => ⟨a y, DFunLike.congr_fun hba y⟩
  have hbi : Function.Injective b := Function.LeftInverse.injective (g := a) fun y => DFunLike.congr_fun hab y
  have hker : RingHom.ker (b.comp W.π) = RingHom.ker W.π := by
    ext x
    simp only [RingHom.mem_ker, AlgHom.comp_apply, map_eq_zero_iff b hbi]
  have hent : ∀ g x y, b (emb (r'.hom (π g)) x y) = emb (B.r.hom g) x y := fun g x y => by
    rw [← hr2, ← hb3]
    exact (congrFun (congrFun (emb_map' (b : R →+* B.R) (r'.hom (π g))) x) y).symm
  refine ⟨⟨W.σ, W.wt, b.comp W.π, hbs.comp W.surj, hker ▸ W.homog⟩, i', τ, κ, inferInstance, inferInstance, e, f, wf,
    ⟨hrel.1, fun x => ?_, hrel.2.2.1, hker.trans hrel.2.2.2⟩, hi' ▸ hpush, fun t => ?_, fun g x y => ?_, fun j => ?_⟩
  · show b (W.π _) = _
    rw [hrel.2.1, ← hb1]
    rfl
  · obtain ⟨x, y, hw, ⟨s, hs⟩ | ⟨v, hv⟩⟩ := hz t
    · obtain ⟨g, rfl⟩ := hq.surjective s
      refine ⟨g, x, y, hw, ?_⟩
      show b (W.z _) = _
      rw [hs, map_sub, AlgHom.commutes, ← hent]
      rfl
    · refine ⟨1, x, y, hw, ?_⟩
      show b (W.z _) = _
      rw [hv, map_one, map_one, map_one]
      by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
  · obtain ⟨p, hp, hp'⟩ := hhom (π g) x y
    refine ⟨p, hp, ?_⟩
    show b (W.π p) = _
    rw [← hent]
    exact congrArg b hp'
  · rw [hκ, hτ]
    exact (hc j).2

end UpperTheory.V.U3
