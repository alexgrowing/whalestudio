import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementIdempotentPartSplitPlaceLatticStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeElementKeepsOneSubIdempotentPartLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPrimeSmulLatticeHeckeElementLeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

end GlobalTheory.HeckeLocStep

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem hat_mono {D : D7} {n : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : L ≤ L') :
    GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin n → D.host.E)) := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, ha, x, h hx, rfl⟩

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem mem_iff_ePart : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    ∀ v ∈ latG V g, (v ∈ M ↔ finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  intro D V P e g M he hPM hMΛ v hv
  obtain ⟨h1, h2, -, -, -, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V g
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) (latG V g) := isNoetherian_of_fg_of_noetherian _ h1
    have hc := (IsNoetherian.noetherian (M.comap (latG V g).subtype)).map (latG V g).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin V.rank → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ h2).symm.le.trans (Submodule.span_mono hPM))
  have hrat := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank M hMfg hMsp).1
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  have hvM : ∀ {w}, w ∈ M → GlobalTheory.AdLat.fv D.host.F w ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E)) :=
    fun hw => (hrat _).2 hw
  constructor
  · intro hm
    exact smul_mem_hat D M hint (hvM hm)
  · intro h
    refine (hrat v).1 ?_
    have hΛ : GlobalTheory.AdLat.fv D.host.F v ∈ GlobalTheory.AdLat.hat D.host.F ((latG V g : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) :=
      ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).2 hv
    have h3 := hat_mono hPM (GlobalTheory.T.one_sub_idempotent_smul_mem_completion_prime_mul D P e V.rank (latG V g) he _ hΛ)
    have hsplit : GlobalTheory.AdLat.fv D.host.F v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]; rfl
    rw [hsplit]
    exact add_mem h h3

theorem mem_latG_iff (D : D7) (V : HSp D) (x : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V x ↔ finVec V v ∈ latGHat V x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V x
  rw [h5]
  exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).symm

theorem exists_hecke : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  obtain ⟨a₀, hH, hloc⟩ := GlobalTheory.T.exists_heckeElement_idempotentPart_splitPlace_lattice D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  refine ⟨a₀, hH, ?_, GlobalTheory.T.conjPrime_smul_lattice_heckeElement_le D V P e ϖ k g a₀ he h1 h2 hH⟩
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  ext v
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨ha, hg⟩
    refine (mem_iff_ePart D V P e g M he hPM hMΛ v hg).2 ((hloc v hg).1 ?_)
    have := (mem_latG_iff D V (g * a₀) v).1 ha
    rw [(GlobalTheory.Member.latG_lattice_and_completion D V (g * a₀)).2.2.2.2.1] at this ⊢
    exact smul_mem_hat D _ hint this
  · intro hv
    have hg := hMΛ hv
    refine ⟨(mem_latG_iff D V (g * a₀) v).2 ?_, hg⟩
    have hsplit : finVec V v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [hsplit]
    exact add_mem ((hloc v hg).2 ((mem_iff_ePart D V P e g M he hPM hMΛ v hg).1 hv))
      (GlobalTheory.T.hecke_element_keeps_one_sub_idempotent_part_lattice D V e ϖ k g a₀ he.1 hH _ ((mem_latG_iff D V g v).1 hg))

end GlobalTheory.HeckeLocStep
