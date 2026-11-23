import Formalism.LocalToGlobal.UnitaryNorms.CharExEta
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharExtend
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdeleUnitsOpen

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

def AlgValsFin (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∃ C : Subfield ℂ, FiniteDimensional ℚ C ∧ χ.ValuesIn s C.subtype

open Formalism.L2.Col

variable {X : Fields} (σ₀ : X.K →+* ℂ)

structure EtaTQc (Φ : Ideles X.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles X.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  unr : ∀ v x, IsUnitAt v x → Φ (localIdele X.E v x) = 1
  resFin : ∀ v k, Φ (aF X.F v k) = etaFin (L := X.E) X.F v k
  resInf : ∀ w k, Φ (aFi X.F w k) = etaInf X.F w k
  inf : ∀ k : X.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ, (X.embC σ₀ τ (k : X.E) / ((‖X.embC σ₀ τ (k : X.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)
  glob : ∀ k : X.Eˣ, diagUnits X.E k ∈ unitF (L := X.E) X.F → Φ (diagUnits X.E k) = 1

theorem etaTExistsC_of (hD : DivExtC) (hO : OpenUnits X.E) {Φ : Ideles X.E →* ℂˣ} (hq : EtaTQc σ₀ Φ) :
    ∃ χ : HChar X.E, Col.IsEtaT X σ₀ χ := by
  obtain ⟨χ, hχ⟩ := exists_hchar_eq_on hD hO (unitF (L := X.E) X.F) le_sup_left Φ hq.cont hq.glob
  have hU : ∀ u ∈ unitIdeles X.E, χ.1 u = Φ u := fun u hu => hχ u (le_sup_left (b := idF (L := X.E) X.F) hu)
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · exact isUnitary_of_unitIdeles χ fun u hu => by rw [hU u hu]; exact hq.unitU u hu
  · intro v x hx
    show χ.1 (localIdele X.E v x) = 1
    rw [hU _ (localIdele_mem hx)]; exact hq.unr v x hx
  · exact ⟨fun v k => by rw [resFin_eq, hχ _ (aF_mem _ v k)]; exact hq.resFin v k,
      fun w k => by rw [resInf_eq, hχ _ (aFi_mem _ w k)]; exact hq.resInf w k⟩
  · intro k
    show ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _
    rw [hU _ (infDiag_mem k)]; exact hq.inf k

structure MuZeroQuasiCharacterCondition {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (e : X.Tau → ℚ) (j : Fin m) (Φ : Ideles X.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles X.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  trivFin : ∀ v k, Φ (aF X.F v k) = 1
  trivInf : ∀ w k, Φ (aFi X.F w k) = 1
  inf : ∃ n : X.Tau → ℤ, (∀ τ, (n τ : ℚ) = 2 * (-e τ)) ∧ ∀ k : X.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ, (X.embC σ₀ τ (k : X.E) / ((‖X.embC σ₀ τ (k : X.E)‖ : ℝ) : ℂ)) ^ n τ
  unr : ∀ v : HeightOneSpectrum (𝓞 X.E), (∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal) → ∀ x, IsUnitAt v x →
    Φ (localIdele X.E v x) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion X.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele X.E v x) = 1
  atg : ∀ (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
    (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y →
    ((Φ (localIdele X.E w.1 (atFin w.1 x)) : ℂˣ) : ℂ) = σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K)
  glob : ∀ k : X.Eˣ, diagUnits X.E k ∈ unitF (L := X.E) X.F → Φ (diagUnits X.E k) = 1

theorem isUnitAt_of_quot {L : Type} [Field L] [NumberField L] {w : HeightOneSpectrum (𝓞 L)} {x : Lˣ} {y : 𝓞 L}
    {c : (𝓞 L ⧸ w.asIdeal)ˣ} (hx : (x : L) = (y : L)) (hc : (c : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y) :
    IsUnitAt w (atFin w x) := by
  have hy : y ∉ w.asIdeal := by
    intro hm
    have h0 : (c : 𝓞 L ⧸ w.asIdeal) = 0 := by rw [hc]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have : Nontrivial (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
    exact c.ne_zero h0
  show Valued.v (algebraMap L (w.adicCompletion L) (x : L)) = 1
  rw [hx]
  exact valued_algebraMap_eq_one L w y hy

theorem mu0ExistsC_of (hD : DivExtC) (hO : OpenUnits X.E) {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {e : X.Tau → ℚ}
    {j : Fin m} {Φ : Ideles X.E →* ℂˣ} (hq : MuZeroQuasiCharacterCondition σ₀ Ch e j Φ) : ∃ χ : HChar X.E, Col.IsMu0 Ch σ₀ e j χ := by
  obtain ⟨χ, hχ⟩ := exists_hchar_eq_on hD hO (unitF (L := X.E) X.F) le_sup_left Φ hq.cont hq.glob
  have hU : ∀ u ∈ unitIdeles X.E, χ.1 u = Φ u := fun u hu => hχ u (le_sup_left (b := idF (L := X.E) X.F) hu)
  have hloc : ∀ v x, IsUnitAt v x → χ.loc v x = Φ (localIdele X.E v x) := fun v x hx => hU _ (localIdele_mem hx)
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isUnitary_of_unitIdeles χ fun u hu => by rw [hU u hu]; exact hq.unitU u hu
  · exact ⟨fun v k => by rw [resFin_eq, hχ _ (aF_mem _ v k)]; exact hq.trivFin v k,
      fun w k => by rw [resInf_eq, hχ _ (aFi_mem _ w k)]; exact hq.trivInf w k⟩
  · obtain ⟨n, hn, hi⟩ := hq.inf
    refine ⟨n, hn, fun k => ?_⟩
    show ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _
    rw [hU _ (infDiag_mem k)]; exact hi k
  · intro v hv x hx
    rw [hloc v x hx]; exact hq.unr v hv x hx
  · intro v x hx h1
    rw [hloc v x hx]; exact hq.tame v x hx h1
  · intro w x y c hx hc
    show ((χ.loc w.1 (atFin w.1 x) : ℂˣ) : ℂ) = _
    rw [hloc w.1 _ (isUnitAt_of_quot hx hc)]; exact hq.atg w x y c hx hc

def cEtaC (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) : ℂˣ :=
  if (aboveF (L := X.E) X.F (P.under (𝓞 X.F))).card = 1 then -1 else 1

def etaValC (k : X.Eˣ) : ℂ :=
  ((unrQ X.E (cEtaC X) (diagUnits X.E k) : ℂˣ) : ℂ) *
    ∏ τ, (X.embC σ₀ τ (k : X.E) / ((‖X.embC σ₀ τ (k : X.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)

def EtaFinCheckC (X : Fields) : Prop := ∀ v k, unrQ X.E (cEtaC X) (aF X.F v k) = etaFin (L := X.E) X.F v k

open Classical in

def EtaInfCheckC : Prop := ∀ (w : InfinitePlace X.F) (k : X.Fˣ),
  (∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (X.embC σ₀ i) ∈ aboveInf (L := X.E) X.F w),
    (X.embC σ₀ i ((upF X.F k : X.Eˣ) : X.E) / ((‖X.embC σ₀ i ((upF X.F k : X.Eˣ) : X.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) =
    ((etaInf X.F w k : ℂˣ) : ℂ)

def GlobFormC (X : Fields) (s0 : X.E) : Prop := ∀ k : X.Eˣ, diagUnits X.E k ∈ unitF (L := X.E) X.F →
  ∃ a : X.Fˣ, k = upF X.F a ∨ ∃ s : X.Eˣ, (s : X.E) = s0 ∧ k = s * upF X.F a

def EtaRecFC : Prop := ∀ a : X.Fˣ, etaValC σ₀ (upF X.F a) = 1

def EtaSqrtDC (s0 : X.E) : Prop := ∀ s : X.Eˣ, (s : X.E) = s0 → etaValC σ₀ s = 1

theorem etaValC_mul (k l : X.Eˣ) : etaValC σ₀ (k * l) = etaValC σ₀ k * etaValC σ₀ l := by
  unfold etaValC
  simp only [zpow_one, Units.val_mul, map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm,
    Finset.prod_mul_distrib]
  ring

theorem etaTExistsC_of_leaves (hD : DivExtC) (hO : OpenUnits X.E) (hI : InfChar (X.embC σ₀) (fun _ => (1 : ℤ)))
    (hF : EtaFinCheckC X) (hIn : EtaInfCheckC σ₀) (s0 : X.E) (h1 : GlobFormC X s0) (h2 : EtaRecFC σ₀)
    (h3 : EtaSqrtDC σ₀ s0) : ∃ χ : HChar X.E, Col.IsEtaT X σ₀ χ := by
  obtain ⟨Φi, hc, hun, hloc, hdiag, hS⟩ := hI
  have hcU : ∀ u ∈ unitIdeles X.E, unrQ X.E (cEtaC X) u = 1 := fun u hu => unrQ_unit _ hu
  have hiF : ∀ v k, Φi (aF X.F v k) = 1 := fun v k => by
    rw [aF, map_prod]; exact Finset.prod_eq_one fun P _ => hloc P _
  have haFi : ∀ w k, aFi (L := X.E) X.F w k ∈ unitIdeles X.E := fun w k =>
    Subgroup.prod_mem _ fun w' _ => (mem_unitIdeles_iff X.E _).mpr (infIdele_mem_rayUnits X.E w' _)
  refine etaTExistsC_of σ₀ hD hO (Φ := unrQ X.E (cEtaC X) * Φi) ⟨(continuous_of_unit hO _ hcU).mul hc, fun u hu => ?_,
    fun v x hx => ?_, fun v k => ?_, fun w k => ?_, fun k => ?_, fun k hk => ?_⟩
  · rw [MonoidHom.mul_apply, hcU u hu, one_mul]; exact hun u
  · rw [MonoidHom.mul_apply, hcU _ (localIdele_mem hx), hloc, one_mul]
  · rw [MonoidHom.mul_apply, hiF, mul_one]; exact hF v k
  · rw [MonoidHom.mul_apply, hcU _ (haFi w k), one_mul]
    apply Units.val_injective
    rw [← hIn w k, aFi]
    exact hS _ _
  · rw [MonoidHom.mul_apply, hcU _ (infDiag_mem k), one_mul, infDiag, MonoidHom.finsetProd_apply]
    simp only [MonoidHom.comp_apply]
    classical
    rw [hS Finset.univ k, Finset.filter_true_of_mem fun i _ => Finset.mem_univ (InfinitePlace.mk (X.embC σ₀ i))]
  · have e : etaValC σ₀ k = 1 := by
      obtain ⟨a, ha | ⟨s, hs, he⟩⟩ := h1 k hk
      · rw [ha]; exact h2 a
      · rw [he, etaValC_mul, h3 s hs, h2 a, one_mul]
    rw [etaValC] at e
    rw [MonoidHom.mul_apply]
    apply Units.val_injective
    rw [Units.val_mul, hdiag k, Units.val_one]
    exact e

theorem etaTExistsC_of_leaves' (hI : InfChar (X.embC σ₀) (fun _ => (1 : ℤ)))
    (hF : EtaFinCheckC X) (hIn : EtaInfCheckC σ₀) (s0 : X.E) (h1 : GlobFormC X s0) (h2 : EtaRecFC σ₀)
    (h3 : EtaSqrtDC σ₀ s0) : ∃ χ : HChar X.E, Col.IsEtaT X σ₀ χ :=
  etaTExistsC_of_leaves σ₀ PI.character_extension_exists (PI.IdeleUnitsOpenW.openUnits X.E) hI hF hIn s0 h1 h2 h3

theorem mu0ExistsC_of' {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {e : X.Tau → ℚ} {j : Fin m} {Φ : Ideles X.E →* ℂˣ}
    (hq : MuZeroQuasiCharacterCondition σ₀ Ch e j Φ) : ∃ χ : HChar X.E, Col.IsMu0 Ch σ₀ e j χ :=
  mu0ExistsC_of σ₀ PI.character_extension_exists (PI.IdeleUnitsOpenW.openUnits X.E) hq

end CharEx

end Formalism.L2.Host
