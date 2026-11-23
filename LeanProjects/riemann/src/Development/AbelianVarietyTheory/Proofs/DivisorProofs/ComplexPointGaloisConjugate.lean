import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondence
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjTransport

theorem coord_unique {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w w' : Fin g → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' := by
  rw [← sub_eq_zero]
  refine GlobalTheory.ArchMetricCompare.eq_zero_of_isDiff u ?_
  intro U hU f
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U :=
    (GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) (GlobalTheory.ArchMetricCompare.isTangent_zero A) U).1 hU
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := (GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv U).2 h0
  rw [GlobalTheory.ArchMetricCompare.isDiff_zero u U hU f, map_zero, map_sub, ← h U hU' f, ← h' U hU' f, sub_self]

theorem coord_exists (hP : GlobalTheory.Published.PeriodComparison) (hD : GlobalTheory.Published.AbelianDeRham) {A : Over (Sp ℂ)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB)
    (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) : ∃ w, u.IsDiff w v := by
  obtain ⟨ε, hP⟩ := hP
  obtain ⟨P, hspan, -, hlie, -⟩ := hP A g hA hg L hL u
  have hE : LieExact A := (hD.2.1 ℂ A g hA hg).1
  have key : ∀ h ∈ Submodule.span ℂ (Set.range P), ∃ (v : epsR ℂ ⟶ A) (w : Fin g → ℂ),
      IsLieImage h v ∧ u.IsDiff w v := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨v, h1, h2⟩ := hlie y
      exact ⟨v, y, h1, h2⟩
    | zero => exact ⟨1, 0, isLieImage_one_iff.2 (zero_mem _), GlobalTheory.UnifDifferential.isDiff_one u⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, w, h1, h2⟩ := hx
      obtain ⟨v', w', h1', h2'⟩ := hy
      exact ⟨v * v', w + w', h1.add h1', GlobalTheory.UnifDifferential.isDiff_mul u ((Chart.isTan_iff _).2 h1.1)
        ((Chart.isTan_iff _).2 h1'.1) h2 h2'⟩
    | smul c x _ hx =>
      obtain ⟨v, w, h1, h2⟩ := hx
      exact ⟨_, c • w, h1.smul c, GlobalTheory.PeriodLattice.isDiff_epsScale u h2 c⟩
  obtain ⟨h, hh⟩ := hE.2 v hv
  obtain ⟨v₁, w, h1, h2⟩ := key h (hspan ▸ Submodule.mem_top)
  exact ⟨w, (hE.1 h).unique h1 hh ▸ h2⟩

theorem grpMor_of_pull {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {A : Over (Sp R)} [GrpObj A]
    {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap σ) φ) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by rw [Category.comp_id, Category.id_comp]) h

theorem exists_corr_symm {R R' : Type} [CommRing R] [CommRing R'] (g : R ≃+* R') {A : Over (Sp R)} [GrpObj A]
    {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {φ : A'.left ⟶ A.left}
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' (g : R →+* R') b φ) (h' : HdR A') :
    ∃ h : HdR A, m.Corr h h' := by
  refine ⟨{ toFun := fun c => g.symm (h' (m.pull c)), map_add' := fun c d => ?_, map_smul' := fun r c => ?_ },
    fun c => ?_⟩
  · simp only [map_add]
  · simp only [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, RingHom.id_apply]
  · simp

theorem exists_corr (hD : GlobalTheory.Published.AbelianDeRham) {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R')
    {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap σ) φ)
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (x : HdR A) : ∃ x', m.Corr x x' := by
  letI : Algebra R R' := σ.toAlgebra
  exact (hD.2.2.1 R A g hA hg R' A' φ h).1.exists x

theorem corr_unique (hD : GlobalTheory.Published.AbelianDeRham) {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R')
    {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap σ) φ)
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {x : HdR A} {x₁ x₂ : HdR A'}
    (h₁ : m.Corr x x₁) (h₂ : m.Corr x x₂) : x₁ = x₂ := by
  letI : Algebra R R' := σ.toAlgebra
  exact (hD.2.2.1 R A g hA hg R' A' φ h).1.unique h₁ h₂

theorem exists_lieCorr (hD : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    (g : ℂ ≃+* ℂ) {X X' : Obj F 𝔠 (Sp ℂ)} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap (g : ℂ →+* ℂ)) p) (v' : X'.Lie) :
    ∃ v : X.Lie, Obj.LieCorr (g : ℂ →+* ℂ) p v v' := by
  have m := grpMor_of_pull (g : ℂ →+* ℂ) hX.grp
  have hE := (hD.2.1 ℂ X.A _ X.ab X.dim).1
  have hE' := (hD.2.1 ℂ X'.A _ X'.ab X'.dim).1
  obtain ⟨h', hh'⟩ := hE'.2 v'.hom v'.isTangent
  obtain ⟨h, hc⟩ := exists_corr_symm g m h'
  obtain ⟨v₀, hv₀, -⟩ := hE.1 h
  exact ⟨Serre.Lie.mk X.rm v₀ hv₀.1, Obj.lieCorr_of_isLieImage hD _ hX m hc hv₀ hh'⟩

end GlobalTheory.ConjTransport

namespace GlobalTheory.ConjTransport

theorem isGrpPullback_inv {S S' : Scheme.{0}} {b : S' ⟶ S} [IsIso b] {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {p : G'.left ⟶ G.left} (hp : IsGrpPullback G' G b p) [IsIso p] :
    IsGrpPullback G G' (inv b) (inv p) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨?_⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  · rw [IsIso.inv_comp_eq, ← Category.assoc, hp.1.w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · let j : Over.mk ((T.hom ≫ inv b) ≫ b) ⟶ T := Over.homMk (𝟙 _) (by simp)
    have e := hp.2 (Over.mk (T.hom ≫ inv b)) x₀ y₀ (j ≫ x) (j ≫ y)
      (by rw [hx]; simp [j]) (by rw [hy]; simp [j])
    rw [← MonObj.comp_mul] at e
    rw [IsIso.eq_comp_inv, ← e]
    simp [j]

theorem exists_conj_hom {S S' : Scheme.{0}} {b : S' ⟶ S} [IsIso b] {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {p : G'.left ⟶ G.left} (hp : IsGrpPullback G' G b p) (α' : G' ⟶ G') [IsMonHom α'] :
    ∃ α : G ⟶ G, IsMonHom α ∧ α'.left ≫ p = p ≫ α.left := by
  haveI : IsIso p := hp.1.isIso_fst_of_isIso
  have w : (inv p ≫ α'.left ≫ p) ≫ G.hom = G.hom := by
    rw [Category.assoc, Category.assoc, hp.1.w, ← Category.assoc α'.left, Over.w α', ← hp.1.w, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  let α : G ⟶ G := Over.homMk (inv p ≫ α'.left ≫ p) w
  refine ⟨α, GlobalTheory.UU.isMonHom_of_over_isMonHom (isGrpPullback_inv hp) (isGrpPullback_inv hp) α' α ?_, ?_⟩
  · simp [α]
  · simp [α]

end GlobalTheory.ConjTransport

namespace GlobalTheory.ConjTransport

theorem exists_polForm {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

end GlobalTheory.ConjTransport

namespace GlobalTheory.ConjTransport

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

theorem low_corr {φ φ' : I → E →+* ℂ} {L L' : Set E} (T : CxPt 𝔠 φ L) (T' : CxPt 𝔠 φ' L') (τ : ℂ →+* ℂ)
    {b : Sp ℂ ⟶ Sp ℂ} {p : T'.X.A.left ⟶ T.X.A.left}
    (m : GrpMor (dp0 ℂ) (𝟙 _) T.X.A (dp0 ℂ) (𝟙 _) T'.X.A τ b p)
    (hψ : ∀ x x' y y', m.Corr x x' → m.Corr y y' → T'.ψ x' y' = τ (T.ψ x y))
    (hy : ∀ i, m.Corr (T.y i) (T'.y i)) (hs : ∀ i, T'.s i = τ (T.s i)) (i : I) {x : HdR T.X.A}
    {x' : HdR T'.X.A} (hx : m.Corr x x') : m.Corr (T.low i x) (T'.low i x') := fun c => by
  simp only [CxPt.low, LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.flip_apply, smul_eq_mul,
    hy i c, hs i, map_mul]
  erw [LinearMap.flip_apply, hψ _ _ _ _ hx (hy i)]
  rfl

end GlobalTheory.ConjTransport

namespace GlobalTheory.ConjTransport

theorem isIso_spMap (g : ℂ ≃+* ℂ) : IsIso (spMap (g : ℂ →+* ℂ)) := by
  have : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) :=
    ⟨⟨CommRingCat.ofHom (g.symm : ℂ →+* ℂ), by ext; simp, by ext; simp⟩⟩
  unfold spMap
  infer_instance

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

theorem isDet_transport (hP : GlobalTheory.Published.PeriodComparison) (hD : GlobalTheory.Published.AbelianDeRham) {φ : I → E →+* ℂ}
    {L L' : Set E} (T : CxPt 𝔠 φ L) (g : ℂ ≃+* ℂ) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
    (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L' 0 X') (κ : ℂ)
    (hX : X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p) (hκ : κ ≠ 0)
    (htan : ∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
          U'.u.IsDiff (fun j ↦ κ * g (w j)) v')
    (δ' : X'.DetGen) (hδ : Obj.DetCorr (g : ℂ →+* ℂ) p T.δ.1 δ'.1) :
    U'.IsDet δ'.1 (g T.C / κ ^ Fintype.card I) := by
  intro v' W' hW'
  choose v hv using fun j => exists_lieCorr hD g hX (v' j)
  choose W hW using fun j => coord_exists hP hD T.X.ab T.X.dim (L := T.X.diag T.U.c)
    (pull_isLB (T.X.isLB T.U.c) _) T.U.u (v j).isTangent
  have hW'' : W' = κ • (g : ℂ →+* ℂ).mapMatrix W := by
    ext j k
    have := coord_unique U'.u (v' j).isTangent (hW' j) (htan (W j) (v j).hom (v' j).hom (hv j) (hW j))
    rw [this]
    rfl
  have hf : Fintype.card (Fin (Module.finrank ℚ (FR E))) = Fintype.card I := Fintype.card_congr T.U.e
  have hd : ((g : ℂ →+* ℂ).mapMatrix W).det = g (Matrix.det W) := (RingHom.map_det _ _).symm
  rw [hδ v v' hv, T.det v W hW, hW'', Matrix.det_smul, hd, map_mul, hf]
  field_simp
  rfl

theorem isCMVec_transport (hD : GlobalTheory.Published.AbelianDeRham) {φ : I → E →+* ℂ} {L L' : Set E} (T : CxPt 𝔠 φ L)
    (g : ℂ ≃+* ℂ) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
    (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L' 0 X') (κ : ℂ)
    (hX : X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p) (he : U'.e = T.U.e)
    (htan : ∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
          U'.u.IsDiff (fun j ↦ κ * g (w j)) v')
    (hend : ∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'],
        α'.left ≫ p = p ≫ α.left → (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
          ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α)
    (i : I) (y' : HdR X'.A) (hy : (grpMor_of_pull (g : ℂ →+* ℂ) hX.grp).Corr (T.y i) y') :
    U'.IsCMVec i y' (κ * g (T.w i)) := by
  have m := grpMor_of_pull (g : ℂ →+* ℂ) hX.grp
  refine ⟨fun a α' _ hα' => ?_, ?_⟩
  · haveI := isIso_spMap g
    obtain ⟨α, hα, hc⟩ := exists_conj_hom hX.grp α'
    haveI := hα
    have h1 := (T.cm i).1 a α (hend a α α' hc hα')
    have h2 : m.Corr (push (dp0 ℂ) (𝟙 _) α (T.y i)) (push (dp0 ℂ) (𝟙 _) α' y') :=
      GrpMor.Corr.push m α α' hc.symm hy
    rw [h1] at h2
    refine corr_unique hD _ T.X.ab T.X.dim hX.grp m h2 (fun c => ?_)
    simp [hy c]
  · obtain ⟨v, hv, hd⟩ := (T.cm i).2
    have hE' := (hD.2.1 ℂ X'.A _ X'.ab X'.dim).1
    obtain ⟨v', hv', -⟩ := hE'.1 y'
    have hl := Obj.lieCorr_of_isLieImage hD _ hX m hy (v := Serre.Lie.mk T.X.rm v hv.1)
      (v' := Serre.Lie.mk X'.rm v' hv'.1) hv hv'
    refine ⟨v', hv', ?_⟩
    have := htan _ v v' hl hd
    convert this using 1
    funext j
    by_cases hj : j = U'.e.symm i
    · subst hj
      simp [he]
    · have hj' : j ≠ T.U.e.symm i := by rwa [← he]
      simp [Pi.single_apply, hj, hj']

end GlobalTheory.ConjTransport

namespace GlobalTheory.ConjTransport

theorem isIso_spMap_dual (g : ℂ ≃+* ℂ) : IsIso (spMap (Chart.dualMapR (g : ℂ →+* ℂ))) := by
  have h1 : ∀ (a b : ℂ ≃+* ℂ), (∀ z, b (a z) = z) → ∀ x, Chart.dualMapR (b : ℂ →+* ℂ) (Chart.dualMapR (a : ℂ →+* ℂ) x) = x :=
    fun a b hab x => TrivSqZeroExt.ext (by simp [Chart.dualMapR, hab]) (by simp [Chart.dualMapR, hab])
  have : IsIso (CommRingCat.ofHom (Chart.dualMapR (g : ℂ →+* ℂ))) :=
    ⟨⟨CommRingCat.ofHom (Chart.dualMapR (g.symm : ℂ →+* ℂ)),
      CommRingCat.hom_ext (RingHom.ext (h1 g g.symm (fun z => g.symm_apply_apply z))),
      CommRingCat.hom_ext (RingHom.ext (h1 g.symm g (fun z => g.apply_symm_apply z)))⟩⟩
  unfold spMap
  infer_instance

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

theorem isOver_transport (hD : GlobalTheory.Published.AbelianDeRham) {φ φ' : I → E →+* ℂ} {L L' : Set E} (T : CxPt 𝔠 φ L)
    (T' : CxPt 𝔠 φ' L') (g : ℂ ≃+* ℂ) (p : T'.X.A.left ⟶ T.X.A.left)
    (hX : T'.X.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p)
    (hδ : Obj.DetCorr (g : ℂ →+* ℂ) p T.δ.1 T'.δ.1)
    (hlow : ∀ i x x', (grpMor_of_pull (g : ℂ →+* ℂ) hX.grp).Corr x x' →
      (grpMor_of_pull (g : ℂ →+* ℂ) hX.grp).Corr (T.low i x) (T'.low i x'))
    {R : Type} [CommRing R] {σ : R →+* ℂ} {X₀ : Obj (FR E) 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (hO : T.IsOver σ X₀ δ₀ N) :
    T'.IsOver ((g : ℂ →+* ℂ).comp σ) X₀ δ₀ N := by
  obtain ⟨p₀, m₀, hX₀, hδ₀, hN⟩ := hO
  have m := grpMor_of_pull (g : ℂ →+* ℂ) hX.grp
  have hX'' : T'.X.IsPullBy X₀ (spMap ((g : ℂ →+* ℂ).comp σ)) (p ≫ p₀) := by
    rw [GlobalTheory.Cris.spMap_comp]
    exact hX.comp hX₀
  have m'' := grpMor_of_pull _ hX''.grp
  refine ⟨p ≫ p₀, m'', hX'', ?_, ?_⟩
  · intro v v'' hc
    choose v' hv' using fun j => exists_lieCorr hD g hX (v'' j)
    have hc₀ : ∀ j, Obj.LieCorr σ p₀ (v j) (v' j) := fun j => by
      have e1 := hc j
      have e2 := hv' j
      unfold Obj.LieCorr at e1 e2 ⊢
      have k : spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (v' j).hom.left ≫ p₀ =
          spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR σ) ≫ (v j).hom.left := by
        rw [← Category.assoc, ← e2, Category.assoc, e1, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
        congr 2
        exact RingHom.ext fun x => TrivSqZeroExt.ext (by simp [Chart.dualMapR]) (by simp [Chart.dualMapR])
      haveI := isIso_spMap_dual g
      exact (cancel_epi _).1 k
    rw [hδ v' v'' hv', hδ₀ v v' hc₀]
    rfl
  · intro i x₀ x'' hc''
    obtain ⟨x, hx⟩ := exists_corr_symm g m x''
    have hx₀ : m₀.Corr x₀ x := fun c => (g : ℂ →+* ℂ).injective (by
      rw [← hx, GrpMor.pull_pull m₀ m m'' (fun _ => rfl) rfl c, hc'']
      rfl)
    have h1 := hN i x₀ x hx₀
    have h2 := hlow i x x'' hx
    intro c
    rw [← GrpMor.pull_pull m₀ m m'' (fun _ => rfl) rfl c, h2 (m₀.pull c), h1 c]
    rfl

theorem exists_conj_point : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ)
    (L L' : Set E) (T : CxPt 𝔠 φ L) (R : Type) [CommRing R] (σ : R →+* ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
    (N : I → Module.End R (HdR X₀.A)), T.IsOver σ X₀ δ₀ N →
    ∀ (g : ℂ ≃+* ℂ) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
      (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L' 0 X') (κ : ℂ),
      X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p → κ ≠ 0 → U'.e = T.U.e → U'.c = T.U.c →
      (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
          U'.u.IsDiff (fun j ↦ κ * g (w j)) v') →
      (∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
        (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
          ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α) →
      ∃ T' : CxPt 𝔠 (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L', T'.IsOver ((g : ℂ →+* ℂ).comp σ) X₀ δ₀ N ∧
        T'.C * κ ^ Fintype.card I = g T.C ∧
        ∀ i, T'.U.h i = U'.h i ∧ T'.s i * T'.w i ^ 2 = κ ^ 2 * g (T.s i * T.w i ^ 2) := by
  intro hP hD _ E _ _ _ I _ 𝔠 φ L L' T R _ σ X₀ δ₀ N hO g X' p U' κ hX hκ he hc htan hend
  have m := grpMor_of_pull (g : ℂ →+* ℂ) hX.grp
  obtain ⟨δ', hδ', -⟩ := hX.existsUnique_detGen _ T.δ
  obtain ⟨ψ', hψ', hψc⟩ := exists_polForm _ hX m T.U.c T.pol
  choose y' hy' using fun i => exists_corr hD _ T.X.ab T.X.dim hX.grp m (T.y i)
  let T' : CxPt 𝔠 (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) L' :=
    { X := X'
      U := U'
      δ := δ'
      C := g T.C / κ ^ Fintype.card I
      det := isDet_transport hP hD T g X' p U' κ hX hκ htan δ' hδ'
      ψ := ψ'
      pol := by rw [hc]; exact hψ'
      y := y'
      w := fun i => κ * g (T.w i)
      s := fun i => g (T.s i)
      cm := fun i => isCMVec_transport hD T g X' p U' κ hX he htan hend i (y' i) (hy' i) }
  refine ⟨T', isOver_transport hD T T' g p hX hδ'
    (fun i x x' hx => low_corr T T' _ m hψc hy' (fun i => rfl) i hx) hO, ?_, fun i => ⟨rfl, ?_⟩⟩
  · show g T.C / κ ^ Fintype.card I * κ ^ Fintype.card I = g T.C
    field_simp
  · show g (T.s i) * (κ * g (T.w i)) ^ 2 = κ ^ 2 * g (T.s i * T.w i ^ 2)
    simp only [map_mul, map_pow]
    ring

end GlobalTheory.ConjTransport
