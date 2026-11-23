import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PLocPrjGOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosetsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonalStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitSwap

open scoped Pointwise

variable {H : Type} [Group H]

set_option quotPrecheck false in
local notation "dg" => ((MonoidHom.id H).prod (MonoidHom.id H))
set_option quotPrecheck false in
local notation "sw" => ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom)

theorem relIndex_sq (A B : Subgroup H) :
    (A.prod A).relIndex (B.prod B) = A.relIndex B * A.relIndex B := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((A.subgroupOf B).prod (A.subgroupOf B))
      (f := (Subgroup.prodEquiv B B).toMonoidHom) (Subgroup.prodEquiv B B).surjective]
  congr 1

def FF (N : H) (f₁ f₂ : H → ℂ) (p : H × H) : ℂ := f₁ (p.1⁻¹ * N * p.2) * f₂ (p.2⁻¹ * p.1)

theorem twist_eq_FF (N : H) (f₁ f₂ : H → ℂ) (f : H × H → ℂ) (hf : ∀ y, f y = f₁ y.1 * f₂ y.2) (p : H × H) :
    f (p⁻¹ * (N, 1) * sw p) = FF N f₁ f₂ p := by
  obtain ⟨x, y⟩ := p
  rw [hf]
  simp [FF]

theorem stab_pair (Z C K L : Subgroup H)
    (hK : ∀ x : H, Z ⊓ K.map (MulAut.conj x).toMonoidHom ≤ C)
    (hL : ∀ x : H, (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) (x : H × H) :
    Z.map dg ⊓ (K.prod K).map (MulAut.conj x).toMonoidHom ≤ C.map dg ∧
      (Z.map dg ⊓ (L.prod L).map (MulAut.conj x).toMonoidHom).relIndex (C.map dg) ≠ 0 := by
  have hinj : Function.Injective dg := fun a b h => congrArg Prod.fst h
  constructor
  · rintro _ ⟨⟨t, ht, rfl⟩, ⟨⟨k₁, k₂⟩, ⟨hk₁, -⟩, he⟩⟩
    refine ⟨t, hK x.1 ⟨ht, k₁, hk₁, congrArg Prod.fst he⟩, rfl⟩
  · have h0 := Subgroup.relIndex_inf_ne_zero (hL x.1) (hL x.2)
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj] at h0
    refine ne_zero_of_dvd_ne_zero h0 (Subgroup.relIndex_dvd_of_le_left _ ?_)
    rintro _ ⟨t, ⟨⟨ht, l₁, hl₁, e₁⟩, ⟨-, l₂, hl₂, e₂⟩⟩, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, (l₁, l₂), ⟨hl₁, hl₂⟩, Prod.ext e₁ e₂⟩

section Top

variable [TopologicalSpace H]

theorem sum_reindex (L : Subgroup H) (N x : H) (f₁ f₂ : H → ℂ) (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂) :
    ∑ᶠ p : H ⧸ L, FF N f₁ f₂ (x, p.out) = ∑ᶠ p : H ⧸ L, f₁ p.out * f₂ (p.out⁻¹ * (x⁻¹ * N * x)) := by
  have hc : ∀ q : H ⧸ L, FF N f₁ f₂ (x, q.out) =
      (fun p : H ⧸ L => f₁ p.out * f₂ (p.out⁻¹ * (x⁻¹ * N * x))) ((x⁻¹ * N) • q) := by
    intro q
    obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul L (x⁻¹ * N * q.out)
    have hq : (x⁻¹ * N) • q = (QuotientGroup.mk (x⁻¹ * N * q.out) : H ⧸ L) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have e : (x⁻¹ * N * q.out * (r : H))⁻¹ * (x⁻¹ * N * x) = (r : H)⁻¹ * (q.out⁻¹ * x) := by group
    simp only [hq, hr, FF]
    rw [e, (h₁.2 _ r.2 _).2, (h₂.2 _ (L.inv_mem r.2) _).1]
  simp_rw [hc]
  exact finsum_comp_equiv (MulAction.toPerm (x⁻¹ * N) : (H ⧸ L) ≃ (H ⧸ L))
    (f := fun p : H ⧸ L => f₁ p.out * f₂ (p.out⁻¹ * (x⁻¹ * N * x)))

theorem sum_eq_hint (K L : Subgroup H) (N x : H) (f₁ f₂ : H → ℂ) (hLK : L ≤ K) (hidx : L.relIndex K ≠ 0)
    (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂) :
    ∑ᶠ p : H ⧸ L, FF N f₁ f₂ (x, p.out) =
      ((L.relIndex K : ℕ) : ℂ) * hint K fun z => f₁ z * f₂ (z⁻¹ * (x⁻¹ * N * x)) := by
  rw [GlobalTheory.T.hecke_integral_finite_sum H K L _ hLK hidx, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hidx), one_mul]
  · exact sum_reindex L N x f₁ f₂ h₁ h₂
  · intro l hl z
    have e : (z * l)⁻¹ * (x⁻¹ * N * x) = l⁻¹ * (z⁻¹ * (x⁻¹ * N * x)) := by group
    show f₁ (z * l) * f₂ ((z * l)⁻¹ * (x⁻¹ * N * x)) = f₁ z * f₂ (z⁻¹ * (x⁻¹ * N * x))
    rw [e, (h₁.2 _ hl _).2, (h₂.2 _ (L.inv_mem hl) _).1]

theorem hecke_tensor (L : Subgroup H) [T2Space H] (f₁ f₂ : H → ℂ) (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂)
    (f : H × H → ℂ) (hf : ∀ y, f y = f₁ y.1 * f₂ y.2) : IsHecke (L.prod L) f := by
  refine ⟨HasCompactSupport.of_support_subset_isCompact (h₁.1.isCompact.prod h₂.1.isCompact) ?_, ?_⟩
  · intro y hy
    rw [Function.mem_support, hf] at hy
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hy), subset_tsupport _ (right_ne_zero_of_mul hy)⟩
  · rintro ⟨k₁, k₂⟩ ⟨hk₁, hk₂⟩ ⟨x, y⟩
    simp only [hf, Prod.mk_mul_mk]
    rw [(h₁.2 _ hk₁ _).1, (h₂.2 _ hk₂ _).1, (h₁.2 _ hk₁ _).2, (h₂.2 _ hk₂ _).2]
    exact ⟨rfl, rfl⟩

variable [IsTopologicalGroup H]

theorem cover {N : H} {f₁ f₂ : H → ℂ}
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂) :
    ∃ D : Set H, IsCompact D ∧ ∀ x z : H, f₁ z ≠ 0 → f₂ (z⁻¹ * (x⁻¹ * N * x)) ≠ 0 →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  obtain ⟨D, hD, h⟩ := hprop (tsupport f₁ * tsupport f₂) (h₁.isCompact.mul h₂.isCompact)
  refine ⟨D, hD, fun x z a b => h x ?_⟩
  have := Set.mul_mem_mul (subset_tsupport _ (Function.mem_support.2 a))
    (subset_tsupport _ (Function.mem_support.2 b))
  rwa [mul_inv_cancel_left] at this

theorem finite_pairs (L : Subgroup H) (hLo : IsOpen (L : Set H)) {N : H} {f₁ f₂ : H → ℂ}
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂) :
    {Q : DoubleCoset.Quotient (((twCent (MonoidHom.id H) N).map dg : Subgroup (H × H)) : Set (H × H))
        ((L.prod L : Subgroup (H × H)) : Set (H × H)) | FF N f₁ f₂ (Quotient.out Q) ≠ 0}.Finite := by
  obtain ⟨D, hD, h⟩ := cover hprop h₁ h₂
  have hD2 : IsCompact ((fun p : H × H => p.1 * p.2⁻¹) '' (D ×ˢ tsupport f₂)) :=
    (hD.prod h₂.isCompact).image (by fun_prop)
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ (L.prod L)
    (by rw [Subgroup.coe_prod]; exact hLo.prod hLo) _ (hD.prod hD2) (fun p => FF N f₁ f₂ p ≠ 0) ?_
  rintro ⟨x, y⟩ hp
  have hp' : f₁ (x⁻¹ * N * y) * f₂ (y⁻¹ * x) ≠ 0 := hp
  have a := left_ne_zero_of_mul hp'
  have b := right_ne_zero_of_mul hp'
  have e₀ : (x⁻¹ * N * y)⁻¹ * (x⁻¹ * N * x) = y⁻¹ * x := by group
  obtain ⟨t, ht, d, hd, e⟩ := h x (x⁻¹ * N * y) a (by rwa [e₀])
  refine ⟨dg t, ⟨t, ht, rfl⟩, (d, d * (y⁻¹ * x)⁻¹),
    ⟨hd, ⟨(d, y⁻¹ * x), ⟨hd, subset_tsupport _ (Function.mem_support.2 b)⟩, rfl⟩⟩, ?_⟩
  refine Prod.ext e ?_
  show y = t * (d * (y⁻¹ * x)⁻¹)
  rw [← mul_assoc, ← e]
  group

theorem finite_single (L : Subgroup H) (hLo : IsOpen (L : Set H)) {N : H} {f₁ f₂ : H → ℂ}
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂) (cv : H → ℂ)
    (hcv : ∀ y, cv y ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0) :
    {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (L : Set H) |
      cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q)) ≠ 0}.Finite := by
  obtain ⟨D, hD, h⟩ := cover hprop h₁ h₂
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ L hLo D hD
    (fun x => cv (x⁻¹ * N * MonoidHom.id H x) ≠ 0) ?_
  intro x hx
  obtain ⟨z, a, b⟩ := hcv _ hx
  exact h x z a b

theorem core [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) (hLo : IsOpen (L : Set H)) (hLK : L ≤ K)
    (h₁ : IsHecke L f₁) (h₂ : IsHecke L f₂) (hG : Good (MonoidHom.id H) K N)
    (hprop : ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
      ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d)
    (f : H × H → ℂ) (hf : ∀ y, f y = f₁ y.1 * f₂ y.2)
    (cv : H → ℂ) (hcv : ∀ y, cv y = hint K fun z => f₁ z * f₂ (z⁻¹ * y)) :
    twOrb sw (K.prod K) (N, 1) f = twOrb (MonoidHom.id H) K N cv := by
  have hI := GlobalTheory.T.rel_index_ne_zero_of_open_le H K L hLo hKc hLK
  have hidx := hI.1
  have hZK : ∀ x : H, twCent (MonoidHom.id H) N ⊓ K.map (MulAut.conj x).toMonoidHom ≤
      cptPart (twCent (MonoidHom.id H) N) := fun x => (hG.2 x).1
  have hZL : ∀ x : H, (twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex
      (cptPart (twCent (MonoidHom.id H) N)) ≠ 0 := fun x => hI.2 _ _ x (hG.2 x).2
  have hle : ∀ x : H, twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj x).toMonoidHom ≤
      cptPart (twCent (MonoidHom.id H) N) := fun x =>
    le_trans (inf_le_inf_left _ (Subgroup.map_mono hLK)) (hZK x)
  have hCZ : cptPart (twCent (MonoidHom.id H) N) ≤ twCent (MonoidHom.id H) N :=
    (Subgroup.closure_le _).2 fun t ht => ht.1
  have hT : twCent sw ((N, 1) : H × H) = (twCent (MonoidHom.id H) N).map dg := GlobalTheory.T.swap_twisted_centralizer_diagonal H N
  have hCp : cptPart (twCent sw ((N, 1) : H × H)) = (cptPart (twCent (MonoidHom.id H) N)).map dg := by
    rw [hT]
    exact GlobalTheory.T.compact_part_diagonal_map H _
  have hfF := twist_eq_FF N f₁ f₂ f hf
  have hK2o : IsOpen ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKo.prod hKo
  have hK2c : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hL2o : IsOpen ((L.prod L : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hLo.prod hLo
  have hfin := finite_pairs L hLo hprop h₁.1 h₂.1 (N := N)
  obtain ⟨A1, A2⟩ := GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel (H × H) sw (K.prod K) hK2o hK2c (fun k hk => ⟨hk.2, hk.1⟩) (L.prod L)
    ⟨hL2o, Subgroup.prod_mono hLK hLK, fun k hk => ⟨hk.2, hk.1⟩⟩ (N, 1) f
    (hecke_tensor L f₁ f₂ h₁ h₂ f hf)
    (by
      intro x
      rw [hCp, hT]
      exact stab_pair _ _ K L hZK hZL x)
    (by
      rw [hT]
      simpa only [hfF] using hfin)
  have hcvf : cv = fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y) := funext hcv
  have hconv := GlobalTheory.T.hecke_convolution_support H K L f₁ f₂ hLK hidx h₁ h₂
  obtain ⟨B1, B2⟩ := GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel H (MonoidHom.id H) K hKo hKc (fun k hk => hk) L
    ⟨hLo, hLK, fun k hk => hk⟩ N cv (hcvf ▸ hconv.1) (fun x => ⟨hZK x, hZL x⟩)
    (finite_single L hLo hprop h₁.1 h₂.1 cv fun y hy => hconv.2 y (by rwa [← hcv]))
  have hcount := GlobalTheory.T.finite_diagonal_double_cosets H (twCent (MonoidHom.id H) N) L (cptPart (twCent (MonoidHom.id H) N))
    (FF N f₁ f₂) (fun x => ⟨hle x, hZL x⟩)
    (fun t ht c hc => by
      rw [hG.1 t ht c (hCZ hc), mul_inv_cancel_right]
      exact hc)
    (fun t ht x y => by
      have e : t * N = N * t := ht
      have e' : (t * x)⁻¹ * N * (t * y) = x⁻¹ * N * y := by
        calc (t * x)⁻¹ * N * (t * y) = x⁻¹ * t⁻¹ * (N * t) * y := by group
          _ = x⁻¹ * t⁻¹ * (t * N) * y := by rw [e]
          _ = x⁻¹ * N * y := by group
      have e'' : (t * y)⁻¹ * (t * x) = y⁻¹ * x := by group
      simp only [FF, e', e''])
    (fun l hl l' hl' x y => by
      have e' : (x * l)⁻¹ * N * (y * l') = l⁻¹ * ((x⁻¹ * N * y) * l') := by group
      have e'' : (y * l')⁻¹ * (x * l) = l'⁻¹ * ((y⁻¹ * x) * l) := by group
      simp only [FF, e', e'']
      rw [(h₁.2 _ (L.inv_mem hl) _).1, (h₁.2 _ hl' _).2, (h₂.2 _ (L.inv_mem hl') _).1, (h₂.2 _ hl _).2])
    hfin
  rw [hCp, hT] at A2
  simp only [hfF] at A2
  have hp : ∀ x : H, ∑ᶠ p : H ⧸ L, FF N f₁ f₂ (x, p.out) =
      ((L.relIndex K : ℕ) : ℂ) * cv (x⁻¹ * N * MonoidHom.id H x) := by
    intro x
    rw [hcv]
    exact sum_eq_hint K L N x f₁ f₂ hLK hidx h₁ h₂
  simp only [hp] at hcount
  rw [A1, A2, hcount, B1, B2, relIndex_sq]
  have hc : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have key := smul_finsum ((L.relIndex K : ℕ) : ℂ) (fun q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (L : Set H) =>
    (((twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
      (cptPart (twCent (MonoidHom.id H) N)) : ℕ) : ℂ) * cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q)))
  simp only [smul_eq_mul] at key
  have key2 : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (L : Set H),
      (((twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) N)) : ℕ) : ℂ) * (((L.relIndex K : ℕ) : ℂ) * cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q))) =
      ((L.relIndex K : ℕ) : ℂ) * ((((twCent (MonoidHom.id H) N ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) N)) : ℕ) : ℂ) * cv ((Quotient.out q)⁻¹ * N * MonoidHom.id H (Quotient.out q))) := fun q => by ring
  simp only [key2]
  rw [← key]
  push_cast
  field_simp

end Top

theorem main : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ),
  IsOpen (K : Set H) → IsCompact (K : Set H) → IsOpen (L : Set H) → L ≤ K → IsHecke L f₁ → IsHecke L f₂ → Good (MonoidHom.id H) K N →
  (∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d) →
  twOrb ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (N, 1) (fun y => f₁ y.1 * f₂ y.2) =
    twOrb (MonoidHom.id H) K N (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  intro H _ _ _ _ K L N f₁ f₂ hKo hKc hLo hLK h₁ h₂ hG hprop
  exact core K L N f₁ f₂ hKo hKc hLo hLK h₁ h₂ hG hprop _ (fun _ => rfl) _ (fun _ => rfl)

end GlobalTheory.CompanionTheory.SplitSwap

end
