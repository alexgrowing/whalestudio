import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutIdA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutId

variable {D : D7} {n : ℕ}

theorem omega_fix {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D W.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)} (hω : IsWeilSch ψ χ θ W μ ω)
    {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) {y : hermA D n} (hy : IntAt v y) (X : Mx D W.rank n) :
    (ω g Ψ).1 X = pch ψ y.1 (ip W X X) * (ω g Ψ).1 X := by
  have e1 : ω (nb y * g) Ψ = ω g Ψ := by
    rw [nb_comm hnb hy.1 hy.2.1 hg, map_mul, Module.End.mul_apply, hΨ _ (nb_mem_KAt hnb hy)]
  have e2 := hω.unip (nb y) y.1 (hnb y) (ω g Ψ) X
  rw [map_mul, Module.End.mul_apply] at e1
  rw [e1] at e2
  exact e2

theorem ip_orbit (W : HSp D) (h : GA D W) (x : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (Formalism.L2.Theta.mt W h) (rat x)) (mm (Formalism.L2.Theta.mt W h) (rat x)) = rat (gramQ W x) := by
  rw [show gramQ W x = GlobalTheory.Unf.gramQ W x from rfl, GlobalTheory.Unf.FB.rat_gramQ]
  simp only [ip, mm]
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA W) (Formalism.L2.Theta.mt W h),
    ← Matrix.mul_assoc (adj (Formalism.L2.Theta.mt W h)), GlobalTheory.MixModel.mt_unitary]

theorem rank_gram_le (W : HSp D) (x : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W x).rank ≤ x.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem law0 {B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D B.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ B.rank n)} (hω : IsWeilSch ψ χ θ B μ ω)
    (Φ : schwartzA θ B.rank n) (s : ℂ) (hs : (B.rank : ℂ) / 2 = s + (n : ℂ) / 2) :
    IsLaw χ s (fun g => (ω g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  show (ω (q * g) Φ).1 0 = _ * _ * (ω g Φ).1 0
  have e' : ω (q * g) Φ = ω m (ω u (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D B.rank n) ⬝ a : Mx D B.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  rw [e', hω.levi m a hm, z1, hω.unip u b hu, z2, ← hs]
  simp [halfTr]

theorem resEta_add {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (k : ℕ) : ResEta D χ (r + 2 * k) :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one]⟩

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    conj (pch ψ x.1 (rat β.1)) = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n))) := by
  have ht : Matrix.trace (mm x.1 (rat β.1)) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n) :=
    Matrix.trace_mul_comm _ _
  change conj (ψ (halfTr (Matrix.trace (mm x.1 (rat β.1))))) = _
  rw [ht, AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]

theorem fc_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n))
    (nb : hermA D n → G D n) (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ x in 𝓖, F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
  change (∫ b in 𝓖, F (nb b * g) * ψ (-halfTr ((β.1.map (incA D) * b.1).trace)) ∂lam) = _
  congr 1
  funext x
  rw [conj_pch hψ]

theorem cont_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) :
    Continuous fun x : hermA D n => conj (pch ψ x.1 (rat β.1)) :=
  Complex.continuous_conj.comp (hψ.1.comp (GlobalTheory.CompanionTheory.FourierN.continuous_halfTr.comp
    ((continuous_subtype_val.matrix_mul continuous_const).matrix_trace)))

theorem norm_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    ‖conj (pch ψ x.1 (rat β.1))‖ ≤ 1 := by
  rw [Complex.norm_conj]
  exact (hψ.2.1 _).le

theorem intOn {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖) {f c : hermA D n → ℂ}
    (hf : Continuous f) (hp : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x) (hc : Continuous c) (hc1 : ∀ x, ‖c x‖ ≤ 1) :
    IntegrableOn (fun x => f x * c x) 𝓖 lam := by
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ x, ‖f x * c x‖ ≤ M := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [norm_mul, ← hp γ hγ x]
    calc ‖f (γ + x)‖ * ‖c x‖ ≤ ‖f (γ + x)‖ * 1 := mul_le_mul_of_nonneg_left (hc1 x) (norm_nonneg _)
      _ ≤ M := by rw [mul_one]; exact hM _ hx
  refine Measure.integrableOn_of_bounded (M := M) ?_ (hf.mul hc).aestronglyMeasurable ?_
  · rw [h.2.2]; exact ENNReal.one_ne_top
  · exact Eventually.of_forall hb

end PositivityTheory.Rg.Rsw.L.LCutId

end
