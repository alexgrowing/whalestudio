import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescentOfLocalGlobalInputs
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem one_lt_absNorm (w : HeightOneSpectrum (𝓞 E)) : 1 < Ideal.absNorm w.asIdeal := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact w.isPrime.ne_top
  omega

theorem norm_absC_val (x : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((GlobalTheory.CuspRep.Model.absC E (x : ℂ)).val w : ℂˣ) : ℂ)‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-x) := by
  rw [PositivityTheory.Rg.Rs.StrStepB.absC_val]
  have h0 : 0 < (Ideal.absNorm w.asIdeal : ℕ) := by
    have := one_lt_absNorm w
    omega
  rw [Complex.norm_natCast_cpow_of_pos h0]
  simp

theorem speh_one {d : ℕ} (h : d = 1) (k : Fin d) : spehExp d k = 0 := by
  subst h
  simp [spehExp]

theorem sum_one {d : ℕ} (h : d = 1) (f : Fin d → Multiset ℂˣ) (k : Fin d) : ∑ i, f i = f k := by
  subst h
  exact Fintype.sum_eq_single k fun i hi => absurd (Subsingleton.elim i k) hi

theorem twist_zero {d a : ℕ} (h : d = 1) (k : Fin d) (P : CuspSub E a) :
    CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d k : ℝ) : ℂ))) = CG.mk P := by
  rw [speh_one h k, Complex.ofReal_zero, PositivityTheory.Rg.Rs.StrStepB.absC_zero, ← CG.twist_mk, CG.twist_one]

theorem hasSat_of_sigma {m n : ℕ} {X : CG E m} {Y : CG E n} (h : (⟨m, X⟩ : Σ k, CG E k) = ⟨n, Y⟩)
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (hX : X.HasSat w B) : Y.HasSat w B := by
  cases h
  exact hX

theorem d_eq_one {a d : ℕ} (P : CuspSub E a) (ha : 1 ≤ a) (hd : 1 ≤ d) (w : HeightOneSpectrum (𝓞 E))
    (b : Fin d → Multiset ℂˣ)
    (hb : ∀ k, (CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d k : ℝ) : ℂ)))).HasSat w (b k))
    (hn : ∀ k, ∀ z ∈ b k, ‖(z : ℂ)‖ = 1) : d = 1 := by
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hk0 : 0 < d := by omega
  have hk1 : d - 1 < d := by omega
  have e : CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨d - 1, hk1⟩ : ℝ) : ℂ))) =
      (CG.mk (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)))).twist
        (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)) := by
    rw [CG.twist_mk, ← CuspSub.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add]
    congr 3
    push_cast
    ring
  have h1 := PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC
    (P.twist (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨0, hk0⟩ : ℝ) : ℂ))) (hb ⟨0, hk0⟩)
    ((spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)
  rw [← e] at h1
  have hu := (hb ⟨d - 1, hk1⟩).unique h1
  obtain ⟨z, hz⟩ : ∃ z, z ∈ b ⟨0, hk0⟩ :=
    Multiset.card_pos_iff_exists_mem.mp (by rw [(hb ⟨0, hk0⟩).card]; omega)
  have hm : z * (GlobalTheory.CuspRep.Model.absC E ((spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ : ℝ) : ℂ)).val w
      ∈ b ⟨d - 1, hk1⟩ := by
    rw [hu]
    exact Multiset.mem_map_of_mem _ hz
  have h2 := hn _ _ hm
  rw [Units.val_mul, norm_mul, hn _ z hz, one_mul, norm_absC_val] at h2
  have hx : spehExp d ⟨d - 1, hk1⟩ - spehExp d ⟨0, hk0⟩ = 1 - (d : ℝ) := by
    simp only [spehExp]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hx] at h2
  have h3 : 1 < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-(1 - (d : ℝ))) := by
    refine Real.one_lt_rpow (by exact_mod_cast one_lt_absNorm w) ?_
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  linarith

theorem split_freq (hC : SplitCore) {n : ℕ} (hn : 1 ≤ n) (π : CG E n) (hu : π.IsUnitary) (ht : Temp π) :
    ∃ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w := by
  show ¬ (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ¬ IsSplitAt w)
  intro h
  obtain ⟨j, -⟩ := hC E n hn π hu ht (Fin 0) (fun _ => 1) (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (h.mono fun w hw hs => absurd hs hw)
  exact j.elim0

theorem rSplitAll : RSplitAll := by
  intro hC hS hStr E _ _ _ n hn π hu ht D hD hL
  choose a d P ha hd hPu hPn hP using hStr E n D hD
  have hAsc : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hP i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have hSt : ∀ i, ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ b : Fin (d i) → Multiset ℂˣ,
      (∀ k, (CG.mk ((P i).twist (GlobalTheory.CuspRep.Model.absC E ((spehExp (d i) k : ℝ) : ℂ)))).HasSat w (b k)) ∧
        GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (D.N i)) ∧ GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (∑ k, b k) :=
    fun i => hS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i) (D.discrete i) (hPu i) (hPn i) (hAsc i)
      (D.loc i) (fun k => GlobalTheory.CuspRep.Model.absC E ((spehExp (d i) k : ℝ) : ℂ))
      (fun k => PositivityTheory.Rg.Rs.InductionInStages.isAbsPow_absC _)
  have hAll := Filter.eventually_all.2 hSt
  have hF := split_freq hC hn (CG.mk π) hu ht
  have hd1 : ∀ i, d i = 1 := by
    intro i
    obtain ⟨w, hw, ⟨b, hb, -, hbs⟩, hl, ⟨B0, hB0, hB0n⟩⟩ := (hF.and_eventually ((hSt i).and (hL.and ht))).exists
    obtain ⟨B, ⟨b', hb', hsum⟩, hB⟩ := hl hw
    have e1 : b' i = ∑ k, b k := (hb' i).2.unique hbs
    have e2 : B0 = B := hB0.unique hB
    refine d_eq_one (P i) (ha i) (hd i) w b hb fun k z hz => hB0n z ?_
    rw [e2, ← hsum]
    exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, by rw [e1]; exact Multiset.mem_sum.2 ⟨k, Finset.mem_univ _, hz⟩⟩
  let k0 : ∀ i, Fin (d i) := fun i => ⟨0, by rw [hd1 i]; exact Nat.one_pos⟩
  have hsp : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ b : Fin D.c → Multiset ℂˣ, (∀ j, (CG.mk (P j)).HasSat w (b j)) ∧ (CG.mk π).HasSat w (∑ j, b j) := by
    refine (hAll.and hL).mono fun w hw hs => ?_
    obtain ⟨hst, hl⟩ := hw
    choose b hb _ hbs using hst
    obtain ⟨B, ⟨b', hb', hsum⟩, hB⟩ := hl hs
    have e : ∀ i, b' i = b i (k0 i) := fun i => ((hb' i).2.unique (hbs i)).trans (sum_one (hd1 i) (b i) (k0 i))
    refine ⟨fun i => b i (k0 i), fun i => ?_, ?_⟩
    · have h1 := hb i (k0 i)
      rwa [twist_zero (hd1 i) (k0 i) (P i)] at h1
    · have h2 : ∑ i, b i (k0 i) = B := by
        rw [← hsum]
        exact Finset.sum_congr rfl fun i _ => (e i).symm
      rw [h2]
      exact hB
  obtain ⟨j, hj⟩ := hC E n hn (CG.mk π) hu ht (Fin D.c) a (fun i => CG.mk (P i)) ha
    (fun i => (CG.isUnitary_mk _).2 (hPu i)) hsp
  have haj : a j = n := congrArg Sigma.fst hj
  have hN : ∀ i, D.N i = a i := fun i => by
    obtain ⟨h, -⟩ := hAsc i
    rw [← h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hd1 i, one_mul]
  have hone : ∀ i, i = j := by
    intro i
    by_contra hij
    have h2 : D.N i + D.N j ≤ ∑ k, D.N k := by
      rw [← Finset.sum_pair hij]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := D.pos i
    rw [D.h, hN j, haj] at h2
    omega
  refine hAll.mono fun w hst => ?_
  choose b hb hsph hbs using hst
  refine ⟨b j (k0 j), ⟨fun i => b i (k0 i), fun i => ⟨hsph i, ?_⟩, ?_⟩, ?_⟩
  · show GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (b i (k0 i))
    rw [← sum_one (hd1 i) (b i) (k0 i)]
    exact hbs i
  · exact Fintype.sum_eq_single j fun i hi => absurd (hone i) hi
  · have h1 := hb j (k0 j)
    rw [twist_zero (hd1 j) (k0 j) (P j)] at h1
    exact hasSat_of_sigma hj h1

end DiscreteGroups.T1.G

end
