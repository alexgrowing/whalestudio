import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc

noncomputable section

namespace GlobalTheory.LieUnif

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre GlobalTheory.EigenSplit Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

theorem trace_add_of_exact {A M₀ M₁ M₂ : Type} [CommRing A] [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module A M₀] [Module A M₁] [Module A M₂] [Module.Free A M₀] [Module.Free A M₁] [Module.Free A M₂]
    [Module.Finite A M₀] [Module.Finite A M₁] [Module.Finite A M₂]
    (i : M₀ →ₗ[A] M₁) (q : M₁ →ₗ[A] M₂) (hi : Function.Injective i) (hex : Function.Exact i q)
    (hq : Function.Surjective q) (f₀ : M₀ →ₗ[A] M₀) (f₁ : M₁ →ₗ[A] M₁) (f₂ : M₂ →ₗ[A] M₂)
    (h₀ : f₁ ∘ₗ i = i ∘ₗ f₀) (h₁ : q ∘ₗ f₁ = f₂ ∘ₗ q) :
    LinearMap.trace A M₁ f₁ = LinearMap.trace A M₀ f₀ + LinearMap.trace A M₂ f₂ := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  have hs' : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  have hk : ∀ x, ∃ y, i y = x - s (q x) := fun x => (hex _).1 (by simp [hs'])
  choose p₀ hp₀ using hk
  let p : M₁ →ₗ[A] M₀ :=
    { toFun := p₀
      map_add' := fun x y => hi (by simp only [map_add, hp₀]; abel)
      map_smul' := fun c x => hi (by simp [hp₀, smul_sub]) }
  have hp : ∀ x, i (p x) = x - s (q x) := hp₀
  have hpi : p ∘ₗ i = LinearMap.id := LinearMap.ext fun y => hi (by
    have : q (i y) = 0 := (hex _).2 ⟨y, rfl⟩
    simp [hp, this])
  have hid : i ∘ₗ p + s ∘ₗ q = LinearMap.id := LinearMap.ext fun x => by simp [hp]
  have t₁ : LinearMap.trace A M₁ (i ∘ₗ (f₀ ∘ₗ p)) = LinearMap.trace A M₀ f₀ := by
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, hpi, LinearMap.comp_id]
  have t₂ : LinearMap.trace A M₁ (s ∘ₗ (q ∘ₗ f₁)) = LinearMap.trace A M₂ f₂ := by
    rw [h₁, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hs, LinearMap.comp_id]
  have t₃ : f₁ = (i ∘ₗ (f₀ ∘ₗ p)) + ((f₁ ∘ₗ s) ∘ₗ q) := LinearMap.ext fun x => by
    have h := LinearMap.congr_fun hid x
    have h' := LinearMap.congr_fun h₀ (p x)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at h h' ⊢
    rw [← h', ← map_add, h]
  have t₄ : LinearMap.trace A M₁ ((f₁ ∘ₗ s) ∘ₗ q) = LinearMap.trace A M₁ (s ∘ₗ (q ∘ₗ f₁)) := by
    rw [LinearMap.trace_comp_comm' q (f₁ ∘ₗ s), LinearMap.trace_comp_comm' (q ∘ₗ f₁) s, LinearMap.comp_assoc]
  conv_lhs => rw [t₃]
  rw [map_add, t₁, t₄, t₂]

theorem trace_map_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (u : Module.End R (Fin n → R)) :
    f (LinearMap.trace R _ u) = ((LinearMap.toMatrix' u)ᵀ.map f).trace := by
  rw [← Matrix.trace_transpose, ← Matrix.transpose_map, Matrix.transpose_transpose, ← AddMonoidHom.map_trace,
    ← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']

theorem trace_lie {A O : Type} [CommRing A] [CommRing O] {G : Over (Sp A)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    {v : Fin n → (epsR A ⟶ G)} (hv : IsLieBasis v) (act : OAct O G) (x : O) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ c, prodPts (c ᵥ* M) v = prodPts c v ≫ act.act x) :
    haveI := Module.Free.of_basis (Lie.basis act hv)
    haveI := Module.Finite.of_basis (Lie.basis act hv)
    LinearMap.trace A (Lie act) (Module.toModuleEnd A (Lie act) x) = M.trace := by
  haveI := Module.Free.of_basis (Lie.basis act hv)
  haveI := Module.Finite.of_basis (Lie.basis act hv)
  let e := (Lie.basis act hv).equivFun
  have he : ∀ c, (e.symm c).hom = prodPts c v := fun c => by
    have h := (Lie.isLieComb_iff c (Lie.basis act hv) (prodPts c v)).1 (by
      simp only [Lie.hom_basis]
      exact (Chart.isLieComb_iff _ _ _).2 rfl)
    rw [h, Module.Basis.equivFun_symm_apply]
  have hconj : e.conj (Module.toModuleEnd A (Lie act) x) = Matrix.toLin' Mᵀ := by
    refine LinearMap.ext fun c => e.symm.injective (Lie.ext ?_)
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, he, Matrix.toLin'_apply, Matrix.mulVec_transpose,
      hM, ← he]
    rfl
  rw [← LinearMap.trace_conj' _ e, hconj, Matrix.trace_toLin'_eq, Matrix.trace_transpose]

theorem map_surjective {A O : Type} [CommRing A] [IsLocalRing A] [CommRing O] {G B : Over (Sp A)} [GrpObj G]
    [GrpObj B] [IsCommMonObj G] [IsCommMonObj B]
    (a : OAct O G) (b : OAct O B) (q : G ⟶ B) [IsMonHom q] [Smooth q.left] :
    Function.Surjective (Lie.map a b q) := by
  intro v
  let π : CommRingCat.of (DualNumber A) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom
  have hπ : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']⟩
  have h0 : η[G].left ≫ q.left = Spec.map π ≫ v.hom.left :=
    (congrArg (·.left) (IsMonHom.one_hom q)).trans v.isTangent.symm
  have : IsLocalRing (DualNumber A) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa [TrivSqZeroExt.isUnit_iff_isUnit_fst] using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair q.left (η[G].left (IsLocalRing.closedPoint A)) (O := ⊤) trivial
  obtain ⟨x, hx, hq⟩ := exists_lift_of_smooth_of_isAffineOpen q.left hU hV hVU π v.hom.left η[G].left h0
    (range_subset_opens_of_isLocalRing _ (by
      have : IsLocalHom π.hom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
      have e : q.left (η[G].left (IsLocalRing.closedPoint A)) =
        v.hom.left (Spec.map π (IsLocalRing.closedPoint A)) := congr($h0 (IsLocalRing.closedPoint A))
      rw [← Spec_closedPoint (f := π), ← e]
      exact hVU hxV))
    (range_subset_opens_of_isLocalRing _ hxV) (by
      intro R S _ _ _ _ _ _ p hp φ
      have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
      have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
        convert hn using 1
        exact Ideal.ext fun b => Eq.congr_left (hp b)
      exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
        Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩)
  exact ⟨Lie.mk a (Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w v.hom)) hx,
    Lie.ext (Over.OverMorphism.ext hq)⟩

theorem trace_level {A O : Type} [CommRing A] [IsLocalRing A] [CommRing O] {K G B : Over (Sp A)} [GrpObj K] [GrpObj G]
    [GrpObj B] [IsCommMonObj K] [IsCommMonObj G] [IsCommMonObj B] {aK : OAct O K} {aG : OAct O G} {aB : OAct O B}
    {i : K ⟶ G} {q : G ⟶ B} (hi : IsLinearHom aK aG i) (hq : IsLinearHom aG aB q)
    (hk : IsPullback i (toUnit K) q η[B]) [Smooth q.left] {r g h : ℕ} {vK : Fin r → (epsR A ⟶ K)}
    {vG : Fin g → (epsR A ⟶ G)} {vB : Fin h → (epsR A ⟶ B)} (hvK : IsLieBasis vK) (hvG : IsLieBasis vG)
    (hvB : IsLieBasis vB) (x : O) (MK : Matrix (Fin r) (Fin r) A) (MG : Matrix (Fin g) (Fin g) A)
    (MB : Matrix (Fin h) (Fin h) A) (hMK : ∀ c, prodPts (c ᵥ* MK) vK = prodPts c vK ≫ aK.act x)
    (hMG : ∀ c, prodPts (c ᵥ* MG) vG = prodPts c vG ≫ aG.act x)
    (hMB : ∀ c, prodPts (c ᵥ* MB) vB = prodPts c vB ≫ aB.act x) :
    MG.trace = MK.trace + MB.trace := by
  have := hi.isMonHom
  have := hq.isMonHom
  haveI := Module.Free.of_basis (Lie.basis aK hvK)
  haveI := Module.Finite.of_basis (Lie.basis aK hvK)
  haveI := Module.Free.of_basis (Lie.basis aG hvG)
  haveI := Module.Finite.of_basis (Lie.basis aG hvG)
  haveI := Module.Free.of_basis (Lie.basis aB hvB)
  haveI := Module.Finite.of_basis (Lie.basis aB hvB)
  obtain ⟨inj, ex⟩ := Lie.map_kernel (a := aG) (b := aB) (c := aK) hk
  rw [← trace_lie hvK aK x MK hMK, ← trace_lie hvG aG x MG hMG, ← trace_lie hvB aB x MB hMB]
  exact trace_add_of_exact (Lie.map aK aG i) (Lie.map aG aB q) inj ex (map_surjective _ _ _) _ _ _
    (LinearMap.ext fun v => (Lie.map_act_smul hi x v).symm) (LinearMap.ext fun v => Lie.map_act_smul hq x v)

theorem trace_eq_sum {F O J N : Type} [Field F] [CommRing O] [Fintype J] [DecidableEq J] [AddCommGroup N] [Module F N]
    [Module.Finite F N] {σ : J → O →+* F} (hσ : IsSplitting σ) (ρ : O →+* Module.End F N) (a : O) :
    LinearMap.trace F N (ρ a) = ∑ j, (Module.finrank F (eigenSub ρ (σ j)) : F) * σ j a := by
  rw [LinearMap.trace_eq_sum_trace_restrict (isInternal_eigenSub hσ ρ) (f := ρ a)
    (fun j x hx => apply_mem_eigenSub hx a)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (ρ a).restrict (fun x hx => apply_mem_eigenSub hx a : ∀ x ∈ eigenSub ρ (σ j), ρ a x ∈ eigenSub ρ (σ j)) =
      σ j a • LinearMap.id := LinearMap.ext fun x => Subtype.ext (mem_eigenSub.1 x.2 a)
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

theorem mult_eq {F O J : Type} [Field F] [CharZero F] [CommRing O] [Fintype J] {σ : J → O →+* F}
    (hσ : Function.Injective σ) (m n : J → ℕ) (r : ℕ)
    (h : ∀ a, ∑ j, (m j : F) * σ j a = ∑ j, (n j : F) * σ j a + ∑ j, (r : F) * σ j a) (j : J) :
    m j = n j + r := by
  have hinj : Function.Injective fun j => (σ j : O →* F) := fun i j hij =>
    hσ (RingHom.ext fun a => DFunLike.congr_fun hij a)
  have hli := (linearIndependent_monoidHom O F).comp _ hinj
  have := Fintype.linearIndependent_iff.1 hli (fun j => (m j : F) - n j - r) (funext fun a => by
    have := h a
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
      Finset.sum_sub_distrib]
    change (∑ j, (m j : F) * σ j a) - (∑ j, (n j : F) * σ j a) - ∑ j, (r : F) * σ j a = 0
    rw [this]; ring) j
  have h' : (m j : F) = ((n j + r : ℕ) : F) := by push_cast; linear_combination this
  exact_mod_cast h'

section Torus

variable {O X k : Type} [CommRing O] [StarRing O] [AddCommGroup X] [Module O X] [CommRing k]

variable (O X k) in

def torusRep : O →+* Module.End k (X →+ k) where
  toFun a := Diag.transpose k (DistribSMul.toAddMonoidHom X (star a))
  map_one' := LinearMap.ext fun c => AddMonoidHom.ext fun x => by simp [Diag.transpose_apply]
  map_mul' a b := LinearMap.ext fun c => AddMonoidHom.ext fun x => by
    simp [Diag.transpose_apply, mul_smul, smul_comm (star a) (star b)]
  map_zero' := LinearMap.ext fun c => AddMonoidHom.ext fun x => by simp [Diag.transpose_apply]
  map_add' a b := LinearMap.ext fun c => AddMonoidHom.ext fun x => by simp [Diag.transpose_apply, add_smul]

def latTrace [Module.Free ℤ X] {r : ℕ} (b : Module.Basis (Fin r) ℤ X) (a : O) : ℤ :=
  (LinearMap.toMatrix b b (DistribSMul.toAddMonoidHom X (star a)).toIntLinearMap).trace

theorem trace_torusRep [Module.Free ℤ X] [Module.Finite ℤ X] {r : ℕ} (b : Module.Basis (Fin r) ℤ X) (a : O) :
    LinearMap.trace k (X →+ k) (torusRep O X k a) = (latTrace b a : k) := by
  rw [LinearMap.trace_eq_matrix_trace k (Diag.dualBasis k b)]
  change (LinearMap.toMatrix _ _ (Diag.transpose k _)).trace = _
  rw [Diag.toMatrix_transpose, Matrix.trace_transpose, latTrace]
  simp [Matrix.trace]

theorem finrank_eigenSub_torusRep {k : Type} [Field k] [IsDomain O] [Module.Finite O X] (τ : O →+* k)
    (hτ : Function.Injective τ) :
    Module.finrank k (eigenSub (torusRep O X k) τ) = Module.finrank O X := by
  obtain ⟨φ⟩ := ConstBasis.nonempty_basis_eigenHom (X := X) (τ.comp (starRingEnd O)) (hτ.comp star_injective)
  have e : eigenSub (torusRep O X k) τ = Diag.eigenHom X (τ.comp (starRingEnd O)) := Submodule.ext fun c => by
    rw [mem_eigenSub]
    constructor
    · intro h a x
      have := DFunLike.congr_fun (h (star a)) x
      simpa [torusRep, Diag.transpose_apply, starRingEnd_apply] using this
    · intro h a
      refine AddMonoidHom.ext fun x => ?_
      have := h (star a) x
      simpa [torusRep, Diag.transpose_apply, starRingEnd_apply] using this
  rw [e, Module.finrank_eq_card_basis φ, Fintype.card_fin]

end Torus

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out in

theorem trace_of_unif {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oD : D.OAct O}
    {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct) [IsCommMonObj D.toPre.P.A]
    [Smooth D.toPre.P.A.hom] {g h r : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {ρ : O →+* Module.End R (Fin g → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ aG.act a)
    {w : Fin h → (epsR R ⟶ D.toPre.P.A)} (hw : IsLieBasis w)
    {ρB : O →+* Module.End R (Fin h → R)}
    (hρB : ∀ a c, prodPts (ρB a c) w = prodPts c w ≫ (ofRingAct oD.onB.toRingAct).act a)
    (b : Module.Basis (Fin r) ℤ D.toPre.X) (a : O) :
    LinearMap.trace R _ (ρ a) = LinearMap.trace R _ (ρB a) + (latTrace b a : R) := by
  have key : ∀ e : ℕ, LinearMap.trace R _ (ρ a) - (LinearMap.trace R _ (ρB a) + (latTrace b a : R)) ∈
      maximalIdeal R ^ (e + 1) := fun e => by
    let f := Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))
    have : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) := by
      have : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
        (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))
      exact IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
    have := U.smooth
    obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
    obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
    let gc := U.gt e
    have := gc.q_hom
    have := gc.i_hom
    have := gc.q_flat
    have := gc.q_surj
    have := gc.q_affine
    have := (H1.torus_dim (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X).smooth
    have : Smooth gc.q.left := by
      refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback gc.i gc.q gc.isKernel).map (Over.forget _)).flip
        ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact gc.q.left)⟩ ?_
      exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
    let aK := @Diag.diagAct (Sp (R ⧸ maximalIdeal R ^ (e + 1))) O _ D.toPre.X _ (Module.compHom _ (starRingEnd O))
    let MK : O → Matrix (Fin r) (Fin r) (R ⧸ maximalIdeal R ^ (e + 1)) := fun x =>
      (LinearMap.toMatrix b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)).toIntLinearMap).map (Int.castRingHom _)
    have hvK := Diag.isLieBasis_dualBasis (R := R ⧸ maximalIdeal R ^ (e + 1)) b
    have hMK : ∀ x i, IsLieComb (MK x i) (fun i => Diag.lieVec (Diag.dualBasis _ b i))
        (Diag.lieVec (Diag.dualBasis _ b i) ≫ aK.act x) := fun x i =>
      Diag.isLieComb_comp_diagMap b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)) i
    have hi : IsLinearHom aK (aG.pullback (thick R _ e) G) gc.i := ⟨inferInstance, fun x => by
      obtain ⟨t, ht, hi⟩ := hl.i_lin e x
      obtain rfl := ConstBasis.eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star x)) ht
      exact hi.symm⟩
    have h := trace_level (K := splitTorus (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X) (aK := aK)
      (aG := aG.pullback (thick R _ e) G) (aB := (ofRingAct oD.onB.toRingAct).pullback (thick R _ e) _)
      (i := gc.i) (q := gc.q) hi ⟨inferInstance, hl.q_lin e⟩ gc.isKernel hvK hv' hw' a
      (MK a) ((LinearMap.toMatrix' (ρ a))ᵀ.map f) ((LinearMap.toMatrix' (ρB a))ᵀ.map f)
      (fun c => (ConstBasis.prodPts_act hvK hMK a c).symm) (fun c => by rw [← hM, hρ']) (fun c => by rw [← hMB, hρB'])
    rw [← Ideal.Quotient.eq, map_add, map_intCast, trace_map_eq, trace_map_eq, h]
    refine (add_comm _ _).trans (congrArg _ ?_)
    simp [MK, latTrace, Matrix.trace]
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_iInf]
  intro n
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (key n)

theorem injective_of_charZero {E F : Type} [Field E] [NumberField E] [Field F] [CharZero F] (τ : 𝓞 E →+* F) :
    Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  obtain ⟨n, hn, d, hd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero h0)
  have := congrArg τ hd
  rw [map_mul, hc, zero_mul] at this
  exact hn (by simpa using this)

theorem lieMult_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (IsLocalRing.maximalIdeal T.V) t) (F : Type) [Field F] [IsAlgClosed F] (f : T.V →+* F), Function.Injective f → ∀ (τ : 𝓞 E →+* F) (N : ℕ), LieMult t.act (spMap f) τ N → letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧ n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  intro E _ _ _ H T t P F _ _ f hf τ N hN
  classical
  letI := H.starRing
  haveI : CharZero F := ⟨fun a b h => Nat.cast_injective (R := T.V) (hf (by simpa using h))⟩
  have := P.U.smooth
  have : Smooth P.D.toPre.P.A.hom := P.D.toPre.P.smoothDim.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis t.G P.U.smooth
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv t.act
  obtain ⟨h, w, hw⟩ := Chart.exists_isLieBasis P.D.toPre.P.A this
  obtain ⟨ρB, hρB⟩ := LieEigen.exists_action hw (ofRingAct P.oD.onB.toRingAct)
  let b := Module.finBasis ℤ P.D.toPre.X
  have htr := trace_of_unif P.U.toUnifPre P.lin hv hρ hw hρB b
  obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
  obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
  let aG := t.act.pullback (spMap f) t.G
  let aB := (ofRingAct P.oD.onB.toRingAct).pullback (spMap f) P.D.toPre.P.A
  haveI := Module.Finite.of_basis (Lie.basis aG hv')
  haveI := Module.Finite.of_basis (Lie.basis aB hw')
  have tG : ∀ a, LinearMap.trace F (Lie aG) (Module.toModuleEnd F (Lie aG) a) = f (LinearMap.trace T.V _ (ρ a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hv' aG a _ (fun c => by rw [← hM, hρ'])
  have tB : ∀ a, LinearMap.trace F (Lie aB) (Module.toModuleEnd F (Lie aB) a) = f (LinearMap.trace T.V _ (ρB a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hw' aB a _ (fun c => by rw [← hMB, hρB'])
  let σ : (E →+* F) → 𝓞 E →+* F := fun i => i.comp (algebraMap (𝓞 E) E)
  have hinj : Function.Injective σ := fun i j hij =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hij
  have hσ : IsSplitting σ := by
    simpa using isSplitting_of_isDomain hinj (NumberField.Embeddings.card E F) (RingHom.id F)
      (isUnit_discr_of_charZero F)
  obtain ⟨j, rfl⟩ : ∃ j, σ j = τ :=
    ⟨IsFractionRing.lift (injective_of_charZero τ), RingHom.ext fun x => IsFractionRing.lift_algebraMap (injective_of_charZero τ) x⟩
  have : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  have he : ∀ {X : Over (Sp F)} [GrpObj X] [IsCommMonObj X] (a : OAct (𝓞 E) X),
      Lie.eig a (σ j) = eigenSub (Module.toModuleEnd F (Lie a)) (σ j) := fun a =>
    Submodule.ext fun v => by rw [mem_eigenSub]; rfl
  have hm := mult_eq hinj (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aG)) (σ i)))
    (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aB)) (σ i)))
    (Module.finrank (𝓞 E) P.D.toPre.X) (fun a => by
      have hT := trace_eq_sum hσ (torusRep (𝓞 E) P.D.toPre.X F) a
      simp only [fun i => finrank_eigenSub_torusRep (X := P.D.toPre.X) (σ i) (injective_of_charZero _)] at hT
      rw [← trace_eq_sum hσ, ← trace_eq_sum hσ, ← hT, tG, tB, htr, trace_torusRep b, map_add, map_intCast]) j
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he] at hN
  refine ⟨_, ?_, hm.symm.trans hN.2⟩
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]
  exact ⟨inferInstance, rfl⟩

end GlobalTheory.LieUnif
