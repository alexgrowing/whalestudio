import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnBaseKer

open Classical in

theorem kerDat_of_isBaseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∀ ω φ, IsBaseKernel R i v (ownAt D v) ω φ → ∃ χ ξR, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu ω φ hK
  obtain ⟨χ, ξR, hchr, hres, hweil, hvec⟩ := hK
  have hD := GlobalTheory.BigOn.isDelta_delAt_ownAt R.C v
  obtain ⟨ψ, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hmem : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), ((n : 𝓞 D.host.E) ∈ P.asIdeal ↔ Formalism.EigenvalueLevelCeiling.plc P ∣ n) :=
    fun P n => by
      unfold Formalism.EigenvalueLevelCeiling.plc
      rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  have hstar : ∀ (n : ℕ) (c : 𝓞 D.host.E), (c : D.host.E) = star ((n : 𝓞 D.host.E) : D.host.E) → c = n := by
    intro n c h
    apply RingOfIntegers.coe_injective
    refine h.trans ?_
    simp
  refine ⟨χ, ξR, ⟨hchr, hD.fin, hD.triv, hD.tame, ?_, ?_, ?_, hres, hweil, hvec⟩⟩
  · intro PP hP
    have hP' := (Finset.mem_filter.1 hP).1
    exact ⟨(hL.Q_pl _ PP hP').1, fun PP' hP'' => (hL.Q_pl _ PP hP').2 PP' (Finset.mem_filter.1 hP'').1⟩
  · intro PP hP
    exact (hL.Q_off _ PP (Finset.mem_filter.1 hP).1).1
  · intro PP
    constructor
    · intro hnu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        by_contra h
        exact hnu (hD.unr PP h)
      have hram : ¬ (R.xiH (R.mu v)).UnrAt PP := by
        rw [hxi]
        intro hu
        obtain ⟨a, ha⟩ := hψ.ord
        have h15 : 15 ∣ Formalism.EigenvalueLevelCeiling.plc v ^ a := by
          refine (hD.ine PP hover _).1 fun x hx => ?_
          have h1 := hu x hx
          rw [Formalism.L2.Host.HChar.loc_mul] at h1
          have h2 : ψ.loc PP x ^ (Formalism.EigenvalueLevelCeiling.plc v ^ a) = 1 := by
            have h3 := congrArg (fun χ' : Formalism.L2.Host.HChar D.host.E => χ'.loc PP x) ha
            exact h3
          rw [eq_inv_of_mul_eq_one_left h1, inv_pow, h2, inv_one]
        have hl := Formalism.EigenvalueLevelCeiling.plc_prime v
        have h3 : 3 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
          (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        have h5 : 5 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1
          (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        omega
      rcases (hL.Q_ram _ PP).1 hram with h | ⟨PP', h, hc⟩
      · exact Or.inl (Finset.mem_filter.2 ⟨h, hover⟩)
      · refine Or.inr ⟨PP', Finset.mem_filter.2 ⟨h, ?_⟩, hc⟩
        obtain ⟨c', hc', he⟩ := hc _ ((hmem PP' _).2 dvd_rfl)
        rw [hstar _ _ he, hmem] at hc'
        have heq := (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime PP) (Formalism.EigenvalueLevelCeiling.plc_prime PP')).1 hc'
        rw [hmem] at hover ⊢
        exact heq ▸ hover
    · intro h hu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        rcases h with h | ⟨PP', h, hc⟩
        · exact (Finset.mem_filter.1 h).2
        · obtain ⟨c', hc', he⟩ := hc _ (Finset.mem_filter.1 h).2
          rwa [hstar _ _ he] at hc'
      have h1 := (hD.ine PP hover 1).1 fun x hx => by rw [pow_one]; exact hu x hx
      norm_num at h1

end GlobalTheory.OnBaseKer

end
