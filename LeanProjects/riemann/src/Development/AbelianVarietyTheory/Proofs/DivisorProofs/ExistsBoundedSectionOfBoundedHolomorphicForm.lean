import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.IntoSec

section Local

variable {n : ℕ}

theorem orth_det {Hm : Mt n} {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀) : x₀.det ≠ 0 ∧ Hm.det ≠ 0 := by
  have h1 := congrArg Matrix.det h.2
  rw [det_mul, det_mul, det_diagonal] at h1
  have h2 : (∏ a : Fin n, -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  rw [← h1] at h2
  exact ⟨right_ne_zero_of_mul h2, right_ne_zero_of_mul (left_ne_zero_of_mul h2)⟩

theorem uh_det {Hm u : Mt n} (hH : Hm.det ≠ 0) (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) : u.det ≠ 0 := by
  have h1 := congrArg Matrix.det (show uᴴ * Hm * u = Hm from hu)
  rw [det_mul] at h1
  rw [← h1] at hH
  exact right_ne_zero_of_mul hH

theorem uh_mul {Hm u v : Mt n} (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) (hv : v ∈ Formalism.QuantumDeterminants.UH Hm) :
    u * v ∈ Formalism.QuantumDeterminants.UH Hm := by
  have h1 : uᴴ * Hm * u = Hm := hu
  have h2 : vᴴ * Hm * v = Hm := hv
  show (u * v)ᴴ * Hm * (u * v) = Hm
  rw [conjTranspose_mul]
  calc vᴴ * uᴴ * Hm * (u * v) = vᴴ * (uᴴ * Hm * u) * v := by simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h1, h2]

theorem uh_inv {Hm u : Mt n} (hH : Hm.det ≠ 0) (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) : u⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  have h1 : uᴴ * Hm * u = Hm := hu
  have hd : IsUnit u.det := (uh_det hH hu).isUnit
  have h3 : u * u⁻¹ = 1 := mul_nonsing_inv _ hd
  show (u⁻¹)ᴴ * Hm * u⁻¹ = Hm
  calc (u⁻¹)ᴴ * Hm * u⁻¹ = (u⁻¹)ᴴ * (uᴴ * Hm * u) * u⁻¹ := by rw [h1]
    _ = (u * u⁻¹)ᴴ * Hm * (u * u⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h3]; simp

theorem upT_one : UpT (1 : Mt n) := ⟨by simp, fun a c h => Matrix.one_apply_ne (ne_of_gt h)⟩

theorem upT_det {b : Mt n} (hb : UpT b) : b.det = ∏ a, b a a :=
  det_of_upperTriangular (fun a c h => hb.2 a c h)

theorem diffOn_prod {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {κ : Type} (t : Finset κ) (f : κ → F → ℂ)
    (s : Set F) (hf : ∀ i, DifferentiableOn ℂ (f i) s) : DifferentiableOn ℂ (fun y => ∏ i ∈ t, f i y) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i).mul ih

theorem det_diff {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : F → Fin n → Fin n → ℂ)
    (hf : ∀ a b, Differentiable ℂ fun y => f y a b) : Differentiable ℂ fun y => (Matrix.of (f y)).det := by
  simp only [det_apply', Matrix.of_apply]
  refine Differentiable.fun_sum fun σ _ => Differentiable.const_mul ?_ _
  rw [← differentiableOn_univ]
  exact diffOn_prod _ (fun i y => f y (σ i) i) _ fun i => (hf _ _).differentiableOn

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_twist (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (h₀ : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (w : ι → Fin n → ℤ) (e : ι → ℤ) (P : (ι → Fin n → Fin n → ℂ) → ℂ) (hP : HolSec Hm q w P)
    (A : ι → Mt n) (hA : A ∈ UG Hm) :
    ∃ Q, HolSec Hm q (fun τ a => w τ a - e τ) Q ∧ ∀ u ∈ UG Hm,
      (∏ τ, (u τ).det ^ e τ) * Q (fun τ => (A τ * u τ * x₀ τ : Mt n)) = P fun τ => (u τ * x₀ τ : Mt n) := by
  obtain ⟨-, -, hst, -⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable n ι Hm q x₀ h₀
  have hH : ∀ τ, (Hm τ).det ≠ 0 := fun τ => (orth_det (h₀ τ)).2
  have hx : ∀ τ, (x₀ τ).det ≠ 0 := fun τ => (orth_det (h₀ τ)).1
  have hAd : ∀ τ, (A τ).det ≠ 0 := fun τ => uh_det (hH τ) (hA τ)
  have hmap : ∀ y ∈ frDoms Hm q, (fun τ => ((A τ)⁻¹ * Matrix.of (y τ) : Mt n)) ∈ frDoms Hm q := by
    intro y hy
    have := hst (fun τ => (A τ)⁻¹) (fun τ => uh_inv (hH τ) (hA τ)) (fun _ => 1) (fun _ => upT_one) y hy
    simpa only [Matrix.mul_one] using this
  refine ⟨fun y => (∏ τ, ((Matrix.of (y τ)).det / ((A τ).det * (x₀ τ).det)) ^ (-e τ)) *
    P (fun τ => ((A τ)⁻¹ * Matrix.of (y τ) : Mt n)), ⟨?_, ?_⟩, ?_⟩
  · refine DifferentiableOn.mul ?_ ?_
    · refine diffOn_prod _ _ _ fun τ => ?_
      refine DifferentiableOn.zpow ?_ (Or.inl fun y hy => div_ne_zero (hy τ).1 (mul_ne_zero (hAd τ) (hx τ)))
      have hd := det_diff (fun y : ι → Fin n → Fin n → ℂ => y τ) fun a b => by fun_prop
      simp only [div_eq_mul_inv]
      exact (hd.mul_const _).differentiableOn
    · have hd : Differentiable ℂ (fun (y : ι → Fin n → Fin n → ℂ) (τ : ι) (a b : Fin n) =>
          ∑ j, (A τ)⁻¹ a j * y τ j b) := by fun_prop
      exact hP.1.comp hd.differentiableOn hmap
  · intro x hx' b hb
    have h1 := hP.2 _ (hmap x hx') b hb
    have h2 : (fun τ => ((A τ)⁻¹ * Matrix.of ((Matrix.of (x τ) * b τ : Mt n)) : Mt n)) =
        fun τ => (Matrix.of (((A τ)⁻¹ * Matrix.of (x τ) : Mt n)) * b τ : Mt n) := by
      funext τ
      exact (Matrix.mul_assoc (A τ)⁻¹ (Matrix.of (x τ)) (b τ)).symm
    beta_reduce
    rw [h2, h1, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h3 : (Matrix.of ((Matrix.of (x τ) * b τ : Mt n))).det = (Matrix.of (x τ)).det * ∏ a, b τ a a := by
      rw [← upT_det (hb τ), ← det_mul]; rfl
    have h4 : ∀ a, b τ a a ≠ 0 := by
      have := (hb τ).1
      rw [upT_det (hb τ)] at this
      exact fun a => Finset.prod_ne_zero_iff.1 this a (Finset.mem_univ a)
    rw [h3, mul_div_right_comm, mul_zpow, ← Finset.prod_zpow, mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← zpow_add₀ (h4 a)]
    congr 1
    ring
  · intro u hu
    beta_reduce
    have h2 : (fun τ => ((A τ)⁻¹ * Matrix.of ((A τ * u τ * x₀ τ : Mt n)) : Mt n)) =
        fun τ => (u τ * x₀ τ : Mt n) := by
      funext τ
      show (A τ)⁻¹ * (A τ * u τ * x₀ τ) = _
      rw [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ (hAd τ).isUnit]
    rw [h2, ← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
    intro τ _
    have h3 : (Matrix.of ((A τ * u τ * x₀ τ : Mt n))).det / ((A τ).det * (x₀ τ).det) = (u τ).det := by
      show (A τ * u τ * x₀ τ).det / _ = _
      rw [det_mul, det_mul]
      field_simp [hAd τ, hx τ]
    rw [h3, ← zpow_add₀ (uh_det (hH τ) (hu τ))]
    simp

theorem exists_decomp (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (h₀ : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (A : ι → Mt n) (hA : A ∈ UG Hm) (y : ι → Fin n → Fin n → ℂ) (hy : y ∈ frDoms Hm q) :
    ∃ u ∈ UG Hm, ∃ b : ι → Mt n, (∀ τ, UpT (b τ)) ∧ ∀ τ, Matrix.of (y τ) = A τ * u τ * x₀ τ * b τ := by
  have hH : ∀ τ, (Hm τ).det ≠ 0 := fun τ => (orth_det (h₀ τ)).2
  have hx : ∀ τ, (x₀ τ).det ≠ 0 := fun τ => (orth_det (h₀ τ)).1
  have hAd : ∀ τ, (A τ).det ≠ 0 := fun τ => uh_det (hH τ) (hA τ)
  choose β hβ using fun τ => GlobalTheory.HolDict.GS.smooth_gramSchmidt n (Hm τ) (q τ) (x₀ τ) (h₀ τ)
  refine ⟨fun τ => (A τ)⁻¹ * (Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹),
    fun τ => uh_mul (uh_inv (hH τ) (hA τ)) ((hβ τ).2 _ (hy τ)).2, fun τ => Matrix.of (β τ (y τ)),
    fun τ => ((hβ τ).2 _ (hy τ)).1, fun τ => ?_⟩
  rw [mul_nonsing_inv_cancel_left _ _ (hAd τ).isUnit, nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
    nonsing_inv_mul_cancel_right _ _ ((hβ τ).2 _ (hy τ)).1.1.isUnit]

end Local

open ReciprocityTheory.ChartRestriction.G.FD in
theorem lact_mul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  show ((γ * γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g h : GA D V) :
    archM V θ (g * h) = archM V θ g * archM V θ h := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

open ReciprocityTheory.ChartRestriction.G.FD in

theorem exists_sec (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (la : ∀ k, Wt (X k).Ψ V.rank) (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (mu : GA D V → ℂ) (c : Comp → ℂ)
    (Kf : Subgroup (GA D V)) (hM : HolShape M) (hG : GoodDict θ M w rfl X la dict mu c Kf) (φ : GA D V → ℂ)
    (hφ : HolForm θ M w (Kf : Set (GA D V)) (fun _ => 1) φ) (k : Comp) :
    ∃ P : Frame (X k).Ψ V.rank → ℂ, (∀ x ∉ (X k).dom, P x = 0) ∧ (X k).IsSec (la k) P ∧
      ∀ g x, dict g = ⟨k, x⟩ → c k * mu g * P x = φ g := by
  classical
  obtain ⟨th, -, -, -, ⟨x0, hx0, -⟩, hdom, -, hlast⟩ := hG.unif
  obtain ⟨h, hh⟩ := (hx0 k).2
  obtain rfl : (dict h).1 = k := by rw [hh]
  clear hh hx0 x0
  obtain ⟨ε, hε, hεd, hεΓ⟩ := GlobalTheory.HolDict.FdDom.dom_iff_frDoms D θ V S M w V.rank rfl Comp X la dict mu c Kf hM hG (dict h).1
  obtain ⟨L, hL, -, -, hUG, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hG.inf
  have h₀ : ∀ ρ, OrthFr (gramAt D V ρ) (nNeg (M.ε ρ)) (x0Mat M ρ) :=
    fun ρ => ((GlobalTheory.HolDict.ModelRep.model_rep D V S M ρ).2.2.2 hM).1
  have hH : ∀ ρ, (gramAt D V ρ).det ≠ 0 := fun ρ => (orth_det (h₀ ρ)).2
  obtain ⟨-, -, hst, hx0d⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable _ _ (gramAt D V) (fun ρ => nNeg (M.ε ρ))
    (x0Mat M) h₀
  obtain ⟨hmul, hnorm, hrat, -⟩ := hG.muUnit
  obtain ⟨e, hmue, hwe⟩ := hG.wt
  obtain ⟨γ, hγ, -, hbase⟩ := hG.base.2.2 h
  obtain ⟨f, ⟨P', hP', hfP⟩, hf⟩ := hφ.hol h
  set A : D.what₂.Tau → Mt V.rank := fun ρ => archM V (θ ρ) (γ * h) with hAdef
  have hA : A ∈ UG (gramAt D V) := hUG (γ * h)
  have hAd : ∀ ρ, (A ρ).det ≠ 0 := fun ρ => uh_det (hH ρ) (hA ρ)
  obtain ⟨Q, hQ, hQP⟩ := exists_twist (gramAt D V) (fun ρ => nNeg (M.ε ρ)) (x0Mat M) h₀ w e P' hP' A hA
  have hmu0 : ∀ g, mu g ≠ 0 := fun g h0 => by simpa [h0] using hnorm g
  let T : Frame (X (dict h).1).Ψ V.rank → (D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ) := fun x ρ => x (ε ρ)
  have hT : ∀ x, x ∈ (X (dict h).1).dom ↔ T x ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ)) := hεd
  have hTinj : ∀ x y, T x = T y → x = y := by
    intro x y hxy
    funext τ
    obtain ⟨ρ, rfl⟩ := ε.surjective τ
    exact congrFun hxy ρ
  have hTl : ∀ δ x ρ, T (lact δ x) ρ =
      ((δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) * Matrix.of (T x ρ) : Mt V.rank) := by
    intro δ x ρ
    rw [← hε ρ]
    rfl
  have hΓ : ∀ δ ∈ (X (dict h).1).Γ, (fun ρ => (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ)) ∈
      UG (gramAt D V) := fun δ hδ ρ => hεΓ δ hδ ρ

  have hunit : ∀ u ∈ UG (gramAt D V), ∀ x, (T x = fun ρ => (A ρ * u ρ * x0Mat M ρ : Mt V.rank)) →
      (∃ γ' ∈ (X (dict h).1).Γ, dict (h * L u) = ⟨(dict h).1, lact γ' x⟩) ∧
        mu (h * L u) * Q (T x) = mu h * φ (h * L u) := by
    intro u hu x hx
    obtain ⟨hLu, hLa⟩ := hL u hu
    constructor
    · obtain ⟨γ', hγ', y, hy, hy'⟩ := hbase (L u) hLu
      refine ⟨γ', hγ', ?_⟩
      rw [hy, hTinj x y]
      rw [hx]
      funext ρ
      have := hy' ρ (ε ρ) (hε ρ)
      rw [archM_mul, hLa] at this
      exact this.symm
    · rw [hf _ hLu, hfP _ (hUG _), hmul, hmue _ hLu, hx, mul_assoc]
      simp only [hLa]
      rw [hQP u hu]
  have hsame : ∀ g g' x, ∀ δ ∈ (X (dict h).1).Γ, dict g = ⟨(dict h).1, x⟩ → dict g' = ⟨(dict h).1, lact δ x⟩ →
      φ g' = φ g ∧ mu g' = mu g := by
    intro g g' x δ hδ hg hg'
    have key : ∀ p : Σ k, Frame (X k).Ψ V.rank, p = ⟨(dict h).1, x⟩ →
        ∃ γ' ∈ (X p.1).Γ, dict g' = ⟨p.1, lact γ' p.2⟩ := by
      rintro p rfl
      exact ⟨δ, hδ, hg'⟩
    obtain ⟨δ0, hδ0, k0, hk0, rfl⟩ := hlast g g' (key _ hg)
    refine ⟨?_, ?_⟩
    · rw [hφ.lev k0 hk0, one_mul, hφ.aut.left _ hδ0]
    · rw [hmul, hmul, hrat _ hδ0, hG.muK _ hk0, one_mul, mul_one]
  have hweight : ∀ x ∈ (X (dict h).1).dom, ∀ b ∈ Bor (X (dict h).1).Ψ V.rank,
      Q (T (rmul x b)) = bchar (la (dict h).1) b * Q (T x) ∧ rmul x b ∈ (X (dict h).1).dom := by
    intro x hx b hb
    have hb' : ∀ ρ, UpT (Matrix.of (T b ρ)) := fun ρ => hb (ε ρ)
    refine ⟨?_, ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom _ hx hb⟩
    have h1 := hQ.2 (T x) ((hT x).1 hx) _ hb'
    refine h1.trans ?_
    congr 1
    unfold bchar
    refine Fintype.prod_equiv ε _ _ fun ρ => Finset.prod_congr rfl fun a _ => ?_
    beta_reduce
    rw [hwe _ ρ (ε ρ) (hε ρ) a, add_sub_cancel_right]
    rfl
  have hinv : ∀ δ ∈ (X (dict h).1).Γ, ∀ x ∈ (X (dict h).1).dom,
      Q (T (lact δ x)) = Q (T x) ∧ lact δ x ∈ (X (dict h).1).dom := by
    intro δ hδ x hx
    have hx' := (hT x).1 hx
    constructor
    · obtain ⟨u, hu, b, hb, hxb⟩ := exists_decomp _ _ _ h₀ A hA (T x) hx'
      let y : Frame (X (dict h).1).Ψ V.rank := fun τ => (A (ε.symm τ) * u (ε.symm τ) * x0Mat M (ε.symm τ) : Mt V.rank)
      have hy : T y = fun ρ => (A ρ * u ρ * x0Mat M ρ : Mt V.rank) := by
        funext ρ
        show (A (ε.symm (ε ρ)) * u (ε.symm (ε ρ)) * x0Mat M (ε.symm (ε ρ)) : Mt V.rank) = _
        rw [Equiv.symm_apply_apply]
      let d : D.what₂.Tau → Mt V.rank := fun ρ => (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ)
      let u' : D.what₂.Tau → Mt V.rank := fun ρ => (A ρ)⁻¹ * (d ρ * (A ρ * u ρ))
      have hu' : u' ∈ UG (gramAt D V) := fun ρ =>
        uh_mul (uh_inv (hH ρ) (hA ρ)) (uh_mul (hΓ δ hδ ρ) (uh_mul (hA ρ) (hu ρ)))
      have hy' : T (lact δ y) = fun ρ => (A ρ * u' ρ * x0Mat M ρ : Mt V.rank) := by
        funext ρ
        rw [hTl, hy]
        show d ρ * (A ρ * u ρ * x0Mat M ρ) = A ρ * ((A ρ)⁻¹ * (d ρ * (A ρ * u ρ))) * x0Mat M ρ
        rw [mul_nonsing_inv_cancel_left _ _ (hAd ρ).isUnit]
        simp only [Matrix.mul_assoc]
      obtain ⟨⟨γ₁, hγ₁, e₁⟩, f₁⟩ := hunit u hu y hy
      obtain ⟨⟨γ₂, hγ₂, e₂⟩, f₂⟩ := hunit u' hu' _ hy'
      have e₃ : lact γ₂ (lact δ y) = lact (γ₂ * δ * γ₁⁻¹) (lact γ₁ y) := by
        rw [← lact_mul, ← lact_mul, inv_mul_cancel_right]
      rw [e₃] at e₂
      obtain ⟨g₁, g₂⟩ := hsame _ _ _ _ (mul_mem (mul_mem hγ₂ hδ) (inv_mem hγ₁)) e₁ e₂
      have hQy : Q (T (lact δ y)) = Q (T y) := by
        apply mul_left_cancel₀ (hmu0 (h * L u))
        rw [f₁, ← g₂, f₂, g₁]
      have hmem : ∀ v ∈ UG (gramAt D V), (fun ρ => (A ρ * v ρ * x0Mat M ρ : Mt V.rank)) ∈
          frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ)) := by
        intro v hv
        have := hst (fun ρ => A ρ * v ρ) (fun ρ => uh_mul (hA ρ) (hv ρ)) (fun _ => 1) (fun _ => upT_one) _ hx0d
        simp only [Matrix.mul_one] at this
        exact this
      have k₁ := hQ.2 (T y) (hy ▸ hmem u hu) b hb
      have k₂ := hQ.2 (T (lact δ y)) (hy' ▸ hmem u' hu') b hb
      have t₁ : T x = fun ρ => (Matrix.of (T y ρ) * b ρ : Mt V.rank) := by
        funext ρ
        rw [hy]
        exact hxb ρ
      have t₂ : T (lact δ x) = fun ρ => (Matrix.of (T (lact δ y) ρ) * b ρ : Mt V.rank) := by
        funext ρ
        rw [hTl, hTl, t₁]
        exact (Matrix.mul_assoc (d ρ) (Matrix.of (T y ρ)) (b ρ)).symm
      rw [t₂, k₂, hQy, ← k₁, ← t₁]
    · rw [hT]
      have := hst _ (hΓ δ hδ) (fun _ => 1) (fun _ => upT_one) _ hx'
      simp only [Matrix.mul_one] at this
      rw [show T (lact δ x) = _ from funext (hTl δ x)]
      exact this
  refine ⟨fun x => if x ∈ (X (dict h).1).dom then (c (dict h).1 * mu h)⁻¹ * Q (T x) else 0,
    fun x hx => if_neg hx, ⟨?_, ?_, ?_⟩, ?_⟩
  · have hd : Differentiable ℂ T := by
      simp only [T]
      fun_prop
    refine ((hQ.1.comp hd.differentiableOn fun x hx => (hT x).1 hx).const_mul (c (dict h).1 * mu h)⁻¹).congr ?_
    intro x hx
    exact if_pos hx
  · intro x hx b hb
    obtain ⟨h1, h2⟩ := hweight x hx b hb
    simp only [if_pos hx, if_pos h2, h1]
    ring
  · intro δ hδ x hx
    obtain ⟨h1, h2⟩ := hinv δ hδ x hx
    simp only [if_pos hx, if_pos h2, h1, hG.chi _ δ hδ, one_mul]
  · intro g x hg
    obtain ⟨γg, -, hfr, -⟩ := hG.base.2.2 g
    have key : ∀ p : Σ k, Frame (X k).Ψ V.rank, p = ⟨(dict h).1, x⟩ → p.2 ∈ (X p.1).dom →
        (∀ ρ (τ : (X p.1).Ψ), τ.1 = tauE D ρ → mat p.2 τ =
          reindex (finCongr rfl) (finCongr rfl) (archM V (θ ρ) (γg * g) * x0Mat M ρ)) →
        x ∈ (X (dict h).1).dom ∧ ∀ ρ, Matrix.of (T x ρ) = archM V (θ ρ) (γg * g) * x0Mat M ρ := by
      rintro p rfl h1 h2
      exact ⟨h1, fun ρ => h2 ρ (ε ρ) (hε ρ)⟩
    obtain ⟨hx, hxa⟩ := key _ hg (hdom g) hfr
    let u : D.what₂.Tau → Mt V.rank := fun ρ => (A ρ)⁻¹ * archM V (θ ρ) (γg * g)
    have hu : u ∈ UG (gramAt D V) := fun ρ => uh_mul (uh_inv (hH ρ) (hA ρ)) (hUG _ ρ)
    have hxu : T x = fun ρ => (A ρ * u ρ * x0Mat M ρ : Mt V.rank) := by
      funext ρ
      show _ = A ρ * ((A ρ)⁻¹ * archM V (θ ρ) (γg * g)) * x0Mat M ρ
      rw [mul_nonsing_inv_cancel_left _ _ (hAd ρ).isUnit]
      exact hxa ρ
    obtain ⟨⟨γ₁, hγ₁, e₁⟩, f₁⟩ := hunit u hu x hxu
    obtain ⟨g₁, g₂⟩ := hsame _ _ _ _ hγ₁ hg e₁
    rw [g₁, g₂] at f₁
    simp only [if_pos hx]
    have := hmu0 h
    have := hG.cNe (dict h).1
    field_simp
    rw [f₁]

open ReciprocityTheory.ChartRestriction.G.FD in

theorem exists_bddSec_adel_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ φ, HolForm θ M w (Kf : Set (GA D V)) (fun _ => 1) φ → ∃ P : FDSec X, P ∈ offZero X ∧ (∀ k, (X k).IsBddSec (la k) (P k)) ∧ adel V dict (muPin V dict mu c) P = φ := by
  intro D θ V S M w r hr Comp X la dict mu c Kf hM hG φ hφ
  subst hr
  choose P hP0 hPs hPφ using exists_sec D θ V S M w Comp X la dict mu c Kf hM hG φ hφ
  refine ⟨P, hP0, fun k => ⟨hPs k, ?_⟩, ?_⟩
  · obtain ⟨C, hC⟩ := hφ.bdd
    obtain ⟨th, -, -, -, -, -, hsurj, -⟩ := hG.unif
    obtain ⟨-, hnorm, -, hdm⟩ := hG.muUnit
    refine ⟨‖c k‖⁻¹ * C, fun x hx => ?_⟩
    obtain ⟨g, γ, hγ, b, hb, hg⟩ := hsurj k x hx
    have h1 : rmul (lact γ x) b = lact γ (rmul x b) := by
      funext τ
      exact Matrix.mul_assoc ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1) (mat x τ) (mat b τ)
    rw [h1] at hg
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Inst.pointwiseNorm_invariance_holds _ (X k) (la k) (P k) (hPs k) γ hγ x hx b hb]
    have key : ∀ p : Σ k, Frame (X k).Ψ V.rank, p = ⟨k, lact γ (rmul x b)⟩ →
        (∀ τ i, ‖dmin (X p.1).Gm p.2 τ i‖ = 1) → ∀ τ i, ‖dmin (X k).Gm (lact γ (rmul x b)) τ i‖ = 1 := by
      rintro p rfl h2
      exact h2
    have h2 := key _ hg (hdm g)
    have h3 := congrArg norm (hPφ k g _ hg)
    rw [norm_mul, norm_mul, hnorm, mul_one] at h3
    have h4 : 0 < ‖c k‖ := norm_pos_iff.2 (hG.cNe k)
    unfold Data.pnorm
    simp only [norm_div, h2, div_one, Real.one_rpow, Finset.prod_const_one, mul_one]
    rw [le_inv_mul_iff₀ h4, h3]
    exact hC g
  · funext g
    exact hPφ (dict g).1 g (dict g).2 rfl

end GlobalTheory.HolDict.IntoSec
