import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
import GroundTheory.AutomorphicForms.IwahoriFactorization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private noncomputable def onSub (ρ : Representation ℂ G V) (Z : Submodule ℂ V)
    (hZ : ∀ g, ∀ v ∈ Z, ρ g v ∈ Z) : Representation ℂ G Z where
  toFun g := (ρ g).restrict (hZ g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

private theorem cosets_finite [TopologicalSpace G] [IsTopologicalGroup G] (I : Subgroup G)
    (hc : IsCompact (I : Set G)) (ho : IsOpen (I : Set G)) (t : G) :
    {c : G ⧸ I | ∃ u ∈ I, c = QuotientGroup.mk (u * t)}.Finite := by
  haveI := QuotientGroup.discreteTopology ho
  have h : IsCompact ((fun u : G => (QuotientGroup.mk (u * t) : G ⧸ I)) '' (I : Set G)) :=
    hc.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))
  refine h.finite_of_discrete.subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private theorem mem_twKer_of_sum (π : Representation ℂ G V) (I N : Subgroup G) (t : G) (v : V)
    (hv : ∀ u ∈ I, π u v = v) (T : Finset (G ⧸ I))
    (hT : ∀ c, c ∈ T ↔ ∃ u ∈ I, c = QuotientGroup.mk (u * t))
    (hfac : ∀ u ∈ I, ∃ x ∈ N, ∃ b ∈ I, u * t = x * t * b)
    (hnorm : ∀ x ∈ N, t⁻¹ * x * t ∈ N)
    (hsum : ∑ c ∈ T, π c.out v = 0) : v ∈ twKer π N 1 := by
  have key : ∀ c ∈ T, π c.out v - π t v ∈ twKer π N 1 := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := (hT c).1 hc
    obtain ⟨x, hx, b, hb, e⟩ := hfac u hu
    obtain ⟨i, hi⟩ := QuotientGroup.mk_out_eq_mul I (u * t)
    have h1 : π (QuotientGroup.mk (u * t) : G ⧸ I).out v = π x (π t v) := by
      rw [hi, e, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Module.End.mul_apply, hv _ i.2, hv _ hb]
    rw [h1]
    exact GlobalTheory.IwahoriInj.sub_mem_twKer hx _
  have h2 : ∑ c ∈ T, (π c.out v - π t v) ∈ twKer π N 1 := Submodule.sum_mem _ key
  rw [Finset.sum_sub_distrib, hsum, zero_sub, neg_mem_iff, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ] at h2
  have hne : (T.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, (hT _).2 ⟨1, one_mem _, by rw [one_mul]⟩⟩)
  have h3 : π t v ∈ twKer π N 1 := (Submodule.smul_mem_iff _ hne).1 h2
  have h4 : twKer π N 1 ≤ (twKer π N 1).comap (π t⁻¹) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, w, rfl⟩
    have e : π t⁻¹ (π (h : G) w - w) =
        π (t⁻¹ * h * t) (π t⁻¹ w) - π t⁻¹ w := by
      rw [map_sub, ← Module.End.mul_apply (π (t⁻¹ * h * t)), ← map_mul,
        ← Module.End.mul_apply (π t⁻¹) (π (h : G)), ← map_mul]
      congr 3
      group
    simpa [e] using GlobalTheory.IwahoriInj.sub_mem_twKer (π := π) (hnorm h h.2) (π t⁻¹ w)
  have h5 := h4 h3
  rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul] at h5
  simpa using h5

end Abstract

section Local

open ValuativeRel Matrix

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

private theorem conj_apply (ν : Fin n → ℤ) (g : GL (Fin n) F) (i j : Fin n) :
    (((Cartan.diagPow F n ν)⁻¹ * g * Cartan.diagPow F n ν : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (ν j - ν i) * (g : Matrix (Fin n) (Fin n) F) i j := by
  have h0 : ((GLnLocal.uniformizer F : 𝒪[F]) : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have e : (((Cartan.diagPow F n ν)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => ((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (-ν i) := rfl
  rw [Units.val_mul, Units.val_mul, e, Cartan.coe_diagPow, mul_diagonal, diagonal_mul,
    sub_eq_add_neg, add_comm, zpow_add₀ h0]
  ring

private theorem conj_mem_iwahori {ν : Fin n → ℤ} (hν : Antitone ν) {b : GL (Fin n) F}
    (hb : b ∈ GLnLocal.iwahori F n)
    (hl : ∀ i j, i < j → (b : Matrix (Fin n) (Fin n) F) i j = 0) :
    (Cartan.diagPow F n ν)⁻¹ * b * Cartan.diagPow F n ν ∈ GLnLocal.iwahori F n := by
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff F n).1 hb
  have hle : ∀ i j, j ≤ i → valuation F
      (((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (ν j - ν i) * (b : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ((b : Matrix (Fin n) (Fin n) F) i j) := fun i j hij => by
    have := Parabolic.valuation_zpow_mul_le_pow_mul (F := F)
      (x := (b : Matrix (Fin n) (Fin n) F) i j) (e := 0) (z := ν j - ν i)
      (by have := hν hij; simp only [Nat.cast_zero]; omega)
    simpa using this
  refine (GLnLocal.mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_apply]
    rcases lt_or_ge i j with h | h
    · rw [hl i j h, mul_zero, map_zero]
      exact zero_le'
    · exact (hle i j h).trans (h1 i j)
  · rw [conj_apply]
    exact (hle i j hij.le).trans_lt (h2 i j hij)
  · rw [conj_apply, sub_self, zpow_zero, one_mul]
    exact h3 i

private theorem conj_mem_unipB (ν : Fin n → ℤ) {x : GL (Fin n) F} (hx : x ∈ unipB F (Fin n)) :
    (Cartan.diagPow F n ν)⁻¹ * x * Cartan.diagPow F n ν ∈ unipB F (Fin n) := by
  obtain ⟨h1, h2⟩ := (mem_unipB F).1 hx
  refine (mem_unipB F).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_apply, h1 i j hij, mul_zero]
  · rw [conj_apply, h2 i, sub_self, zpow_zero, one_mul]

private theorem iwahori_le (g : GL (Fin n) F) (hg : g ∈ iwahori F (Fin n)) :
    g ∈ GLnLocal.iwahori F n := by
  obtain ⟨u, hu, rfl⟩ := hg
  refine ⟨u, ?_, ?_⟩
  · refine Subgroup.mem_comap.2 ((GroundTheory.Automorphic.mem_borel_iff _).2 fun i j hij => ?_)
    rw [GLnLocal.residueReduction_apply]
    exact (GlobalTheory.SmGL.mem_borel _).1 hu i j hij
  · refine Units.ext ?_
    ext i j
    rfl

private theorem factor {ν : Fin n → ℤ} (hν : Antitone ν) (u : GL (Fin n) F)
    (hu : u ∈ GLnLocal.iwahori F n) :
    ∃ x ∈ unipB F (Fin n), ∃ b ∈ GLnLocal.iwahori F n,
      u * Cartan.diagPow F n ν = x * Cartan.diagPow F n ν * b := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id u hu
  obtain ⟨hxP, hx1⟩ := Parabolic.mem_unipotentRadical.1 hx.2
  have hyL := Parabolic.mem_levi.1 hy.2
  obtain ⟨hz0, -⟩ := Parabolic.mem_oppositeUnipotentRadical.1 hz.2
  refine ⟨x, (mem_unipB F).2 ⟨fun i j hij => hxP hij, fun i => ?_⟩, _,
    mul_mem (conj_mem_iwahori hν hy.1 fun i j h => hyL i j h.ne)
      (conj_mem_iwahori hν hz.1 fun i j h => hz0 i j h), ?_⟩
  · simpa using hx1 i i rfl
  · group

private theorem local_inj {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (Z : Submodule ℂ V) (hZ : ∀ g, ∀ v ∈ Z, ρ g v ∈ Z)
    (hsm : ∀ v ∈ Z, IsOpen {g | ρ g v = v}) (ν : Fin n → ℤ) (hν : Antitone ν) (v : V) (hvZ : v ∈ Z)
    (hv : ∀ u ∈ GLnLocal.iwahori F n, ρ u v = v)
    (h0 : hopR ρ (GLnLocal.iwahori F n) (Cartan.diagPow F n ν) v = 0) : v = 0 := by
  have hS := cosets_finite (GLnLocal.iwahori F n) (GLnLocal.isCompact_iwahori F n)
    (GLnLocal.isOpen_iwahori F n) (Cartan.diagPow F n ν)
  have h1 : ∑ c ∈ hS.toFinset, ρ c.out v = 0 := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hS]
    exact h0
  let π := onSub ρ Z hZ
  have hπ : ∀ (g : GL (Fin n) F) (a : Z), ((π g a : Z) : V) = ρ g a := fun _ _ => rfl
  have hsmooth : GlobalTheory.PRep.IsSmooth π := fun a => by
    have : {g : GL (Fin n) F | π g a = a} = {g | ρ g a = a} := by
      ext g
      exact Subtype.ext_iff
    rw [this]
    exact hsm a a.2
  have hker : (⟨v, hvZ⟩ : Z) ∈ twKer π (unipB F (Fin n)) 1 := by
    refine mem_twKer_of_sum π (GLnLocal.iwahori F n) _ (Cartan.diagPow F n ν) _
      (fun u hu => Subtype.ext (hv u hu)) hS.toFinset (fun c => by simp)
      (factor hν) (fun x hx => conj_mem_unipB ν hx) (Subtype.ext ?_)
    rw [Submodule.coe_sum]
    exact h1
  have hfix : (⟨v, hvZ⟩ : Z) ∈ fixed π (iwahori F (Fin n)) :=
    GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => Subtype.ext (hv h (iwahori_le h hh))
  have h2 := (injective_iff_map_eq_zero _).1
    (GlobalTheory.IwahoriInj.iwahoriProj_injective F (Fin n) Z π hsmooth) ⟨_, hfix⟩
    (Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 hker))
  exact congrArg (fun a : fixed π (iwahori F (Fin n)) => ((a : Z) : V)) h2

end Local

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.iwInj :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (w : Pl K) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Gw n w) V) (Z : Submodule ℂ V), (∀ g, ∀ v ∈ Z, ρ g v ∈ Z) →
      (∀ v ∈ Z, IsOpen {g | ρ g v = v}) → ∀ ν : Fin n → ℤ, Antitone ν → ∀ v ∈ Z, (∀ u ∈ GLnLocal.iwahori (w.adicCompletion K) n, ρ u v = v) →
        hopR ρ (GLnLocal.iwahori (w.adicCompletion K) n) (Cartan.diagPow (w.adicCompletion K) n ν) v = 0 → v = 0 := by
  intro K _ _ n w V _ _ ρ Z hZ hsm ν hν v hvZ hv h0
  exact UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection.local_inj ρ Z hZ hsm ν hν v hvZ hv h0
