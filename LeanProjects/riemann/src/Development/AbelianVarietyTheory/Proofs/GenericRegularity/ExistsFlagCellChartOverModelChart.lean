import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFractionField
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NonemptyLift
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankEqOfExistsUniqueComb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieIntegral
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularInvOfDiagNe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsOpenImmersionOfSurj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppLEInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.CellChart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}

theorem lift_point_unique {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x x' : Sp R ⟶ Xo.X}
    (Λ : M.Lift f x) (Λ' : M.Lift f x') : x = x' := by
  haveI := Y.jQ_open
  have h : Λ.xF = Λ'.xF := by
    rw [← cancel_mono Y.jQ]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact Λ.xF_j.trans Λ'.xF_j.symm
    · rw [Category.assoc, Category.assoc, Y.jQ_over]
      exact Λ.xF_snd.trans Λ'.xF_snd.symm
  rw [← Λ.xF_fst, h, Λ'.xF_fst]

theorem tie_unique {L : Type} [Field L] [Algebra c.F L] {f : Γ(Y.X, M.U) →+* L}
    {u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L} {y z : FrPt Xo c L} (hy : M.Comparison₂ f u y)
    (hz : M.Comparison₂ f u z) : y = z :=
  GlobalTheory.Reg.TieUniq.frPt_eq_of_tie E H Dw l Xo c O β Y M L f u y z hy hz (lift_point_unique hy.choose hz.choose)

theorem tie_congr {R : Type} [CommRing R] [Algebra c.F R] {f f' : Γ(Y.X, M.U) →+* R}
    {u u' : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R} {y : FrPt Xo c R} (hy : M.Comparison₂ f u y)
    (hf : ∀ a, f a = f' a) (hu : ∀ τ i j, u τ i j = u' τ i j) : M.Comparison₂ f' u' y := by
  obtain rfl : f = f' := RingHom.ext hf
  obtain rfl : u = u' := funext fun τ => Matrix.ext (hu τ)
  exact hy

end

theorem mul_eq_smul_iff_cols {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin n) R) (N : R)
    (u : Matrix (Fin n) (Fin r) R) : P * u = N • u ↔ ∀ i, P.mulVec (fun j => u j i) = N • fun j => u j i :=
  ⟨fun h i => funext fun j => congrFun (congrFun h j) i, fun h => Matrix.ext fun j i => congrFun (h i) j⟩

end GlobalTheory.Reg.CellChart

namespace GlobalTheory.Reg

open GlobalTheory.Reg.CellChart in

theorem exists_pChart_of_cell : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∀ (M : MChart Y) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n), ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), (∀ a, f a ∈ W) → (∀ τ i j, u τ i j ∈ W) → (∀ τ, InCell (ix τ) (u τ)) → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → ∃ j, (P j).Catches W y := by
  intro hS E _ _ _ H Dw l Xo c hbc O _ _ _ _ _ Y hpush M ix
  haveI := M.dom
  obtain ⟨α, es, -, hft, hinj, hne, hes, hop, hpt⟩ := GlobalTheory.Reg.ChartOpens.moduli_basicOpens E H Dw l Xo c O Y M
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c O _ Y M
  have hemb : Function.Injective (embF (E := E) c) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a)
  choose N p hN hp using exists_projector E c.F (embF c) hemb O Γ(Y.X, M.U) α M.n ρ
  have heig : ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → ∀ τ x,
        M.Eig f τ x ↔ ((p τ).map f).mulVec x = f (α (N τ)) • x := by
    intro R _ _ f hf τ x
    rw [← (hp τ R f hf).2 x]
    simp only [hρ]
    rfl
  have hfN : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) → ∀ τ, f (α (N τ)) ≠ 0 := by
    intro L _ _ f hf τ
    rw [show f (α (N τ)) = algebraMap c.F L (algebraMap O c.F (N τ)) from RingHom.congr_fun hf _]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective O c.F)).mpr (hN τ))
  have hlift : ∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → ∃ x, Nonempty (M.Lift f x) := by
    intro e he R _ _ f hf hu
    obtain ⟨xF, h1, h2⟩ := (hop e he R f hf hu).1
    exact ⟨_, MChart.nonempty_lift E H Dw l Xo c O _ Y M R f xF h1 h2⟩
  have hrk : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) →
      ∀ e ∈ es, f e ≠ 0 → ∀ τ, ((p τ).map f).rank = Dw.mult τ := by
    intro L _ _ f hf e he hfe τ
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e he L f hf hfe.isUnit
    let S : Submodule L (Fin M.n → L) := Module.End.eigenspace ((p τ).map f).mulVecLin (f (α (N τ)))
    have hS' : ∀ y, y ∈ S ↔ ((p τ).map f).mulVec y = f (α (N τ)) • y := fun y => Module.End.mem_eigenspace_iff
    rw [rank_of_quasi_idem _ _ (hfN L f hf τ) (hp τ L f hf).1 S hS']
    exact GlobalTheory.Reg.finrank_chart_eig E H Dw l Xo c O _ Y M L f x Λ τ S fun y => (hS' y).trans (heig L f hf τ y).symm
  have hpoint : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L)
      (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L)
      (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L),
      (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u →
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ (∃ e ∈ es, f e ≠ 0) ∧
        ∀ τ, (p τ).map f * u τ = f (α (N τ)) • u τ := by
    intro L _ _ f y Λ u b hb ht
    obtain ⟨hf, he⟩ := hpt L f Λ.xF Λ.xF_snd Λ.xF_j
    refine ⟨hf, he, fun τ => ?_⟩
    have h1 : (p τ).map f * (u τ * b τ) = f (α (N τ)) • (u τ * b τ) :=
      (mul_eq_smul_iff_cols _ _ _).mpr fun i => (heig L f hf τ _).mp
        ((GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O _ Y M L f y.x Λ τ _ _ (ht τ i)).mp (y.eig τ i))
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hb τ).1]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => (hb τ).2 i).isUnit
    have h2 := congrArg (· * (b τ)⁻¹) h1
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one] at h2
    exact h2
  by_cases hκ : ∃ κ₀ : ∀ τ, Fin (Dw.mult τ) → Fin M.n, ∀ τ, ((p τ).submatrix (ix τ) (κ₀ τ)).det ≠ 0
  swap
  · refine ⟨Empty, inferInstance, Empty.elim, fun L _ _ W f y Λ u b _ _ hc hb ht => (hκ ?_).elim⟩
    obtain ⟨hf, -, hu⟩ := hpoint L f y Λ u b hb ht
    choose κ hκL using fun τ => exists_minor _ _ (hfN L f hf τ) (ix τ) (u τ) (hu τ) (hc τ)
    refine ⟨κ, fun τ h => hκL τ ?_⟩
    have := RingHom.map_det f ((p τ).submatrix (ix τ) (κ τ))
    rw [h, map_zero] at this
    exact this.symm
  obtain ⟨κ₀, hκ₀⟩ := hκ
  obtain ⟨Ω, _, _, gens, es', g, u, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_cell_algebra c.F O Γ(Y.X, M.U) (E →+* ℂ) α hft hinj es hes hne M.n Dw.mult ix N hN p
      (fun L _ _ f hf τ => (hp τ L f hf).1) hrk (fun e he R _ _ f hf hu => (hop e he R f hf hu).2) κ₀ hκ₀
  choose hsm fe ue k1 k2 k3 k4 k5 k6 using h8
  have hy : ∀ e (he : e ∈ es'), ∃ y : FrPt Xo c (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))),
      M.Comparison₂ (fe e he) (ue e he) y := by
    intro e he
    obtain ⟨e₀, he₀, hu⟩ := k4 e he
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e₀ he₀ _ (fe e he) (k3 e he) hu
    obtain ⟨y, -, hy⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c O _ Y M _ (fe e he) x Λ (ue e he)
      (fun τ i => (heig _ _ (k3 e he) τ _).mpr ((mul_eq_smul_iff_cols _ _ _).mp (k5 e he τ) i))
      (fun τ cv h => k6 e he τ cv ((heig _ _ (k3 e he) τ _).mp h))
    exact ⟨y, hy⟩
  choose yy hyy using hy
  have hgen : ∀ e (he : e ∈ es') z, FrMap (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he) z →
      M.Comparison₂ g u z := fun e he z hz =>
    tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (k1 e he) (k2 e he)
  obtain ⟨e₁, he₁⟩ := id h2
  obtain ⟨yg, hyg⟩ := hbc _ _ (Algebra.adjoin c.F (insert e₁⁻¹ (gens : Set Ω))).val (yy e₁ he₁)
  have hint : ∀ e (he : e ∈ es') (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
      ∀ (ψ : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)) →ₐ[c.F] T.Fr),
        (∀ a : O, io (algebraMap O c.F a) ∈ Set.range (algebraMap T.V T.Fr)) →
        (∀ w : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)), (w : Ω) ∈ gens →
          ψ w ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ z : FrPt Xo c T.Fr, FrMap ψ (yy e he) z → Integral T io z := by
    intro e he T io
    letI := io.toAlgebra
    intro ψ hO hg z hz
    have hVinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
    have hB : ∀ w ∈ Subring.closure (Set.range ((algebraMap c.F Ω).comp (algebraMap O c.F)) ∪ (gens : Set Ω)),
        w ∈ (((algebraMap T.V T.Fr).range.comap ψ.toRingHom).map
          (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val.toRingHom) := by
      intro w hw
      refine (Subring.closure_le.mpr ?_) hw
      rintro w (⟨o, rfl⟩ | hw)
      · refine ⟨algebraMap c.F _ (algebraMap O c.F o), ?_, rfl⟩
        obtain ⟨v, hv⟩ := hO o
        exact ⟨v, hv.trans (ψ.commutes _).symm⟩
      · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
    have hfa : ∀ a, ψ.toRingHom.comp (fe e he) a ∈ (algebraMap T.V T.Fr).range := by
      intro a
      obtain ⟨w, hw, hw'⟩ := hB _ (h4 a)
      obtain rfl : w = fe e he a := Subtype.ext (hw'.trans (k1 e he a).symm)
      exact hw
    let φ := (algebraMap T.V T.Fr).rangeRestrict
    let ε : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective φ
      ⟨fun a b h => hVinj (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    let f₀ : Γ(Y.X, M.U) →+* T.V := ε.symm.toRingHom.comp ((ψ.toRingHom.comp (fe e he)).codRestrict _ hfa)
    have hf₀ : ∀ a, algebraMap T.V T.Fr (f₀ a) = ψ (fe e he a) := fun a =>
      congrArg Subtype.val (ε.apply_symm_apply ⟨_, hfa a⟩)
    choose u₀ hu₀ using fun τ i j => hg (ue e he τ i j) (by rw [k2]; exact h5 τ i j)
    refine GlobalTheory.Reg.tie_integral hS E H Dw l Xo c O _ Y M hpush T io f₀ ix u₀ (fun τ => ⟨fun i j hij => hVinj ?_,
      fun i => hVinj ?_⟩) z (tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz)
        (fun a => (hf₀ a).symm) fun τ i j => (hu₀ τ i j).symm)
    · rw [hu₀, show ue e he τ (ix τ i) j = 0 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).1 i j hij)),
        map_zero, map_zero]
    · rw [hu₀, show ue e he τ (ix τ i) i = 1 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).2 i)),
        map_one, map_one]
  let P : PChart Xo c (algebraMap O c.F) :=
    { Ω := Ω, gens := gens, frac := h1, es := es', es_ne := h2, es_mem := h3, sm := hsm, yg := yg, y := yy
      gen := fun e he => by
        obtain ⟨z, hz⟩ := hbc _ _ (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he)
        rw [tie_unique (hgen _ _ _ hyg) (hgen _ _ _ hz)]
        exact hz
      int := hint }
  refine ⟨Unit, inferInstance, fun _ => P, fun L _ _ W f y Λ u' b hW hW' hc hb ht => ⟨(), ?_⟩⟩
  obtain ⟨hf, ⟨e₀, he₀, hfe⟩, hu⟩ := hpoint L f y Λ u' b hb ht
  obtain ⟨e, he, ψ, hψ1, hψ2⟩ := h9 L f hf e₀ he₀ hfe u' hu hc
  obtain ⟨z, hz⟩ := hbc _ _ ψ (yy e he)
  have htz : M.Comparison₂ f u' z := by
    refine tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (fun a => ?_) fun τ i j => ?_
    · exact (congrArg ψ (Subtype.ext (k1 e he a))).trans (hψ1 a (k1 e he a ▸ (fe e he a).2))
    · exact (congrArg ψ (Subtype.ext (k2 e he τ i j))).trans (hψ2 τ i j (k2 e he τ i j ▸ (ue e he τ i j).2))
  obtain ⟨t, ht'⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c O _ Y M L f y z Λ u' b (lift_point_unique htz.choose Λ) hb ht htz
  refine ⟨e, he, ψ, z, t, ?_, hz, ht'⟩
  rintro ⟨w, hw⟩ hwg
  rcases h6 w hwg with ⟨a, rfl⟩ | ⟨τ, i, j, rfl⟩
  · exact (hψ1 a hw).symm ▸ hW a
  · exact (hψ2 τ i j hw).symm ▸ hW' τ i j

end GlobalTheory.Reg
