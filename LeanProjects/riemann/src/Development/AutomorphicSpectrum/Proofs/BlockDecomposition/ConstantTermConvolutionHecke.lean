import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTerm

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.ConvMat

section Generic

theorem hint_const_mul {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) (c : ℂ) :
    hint K (fun z => c * u z) = c * hint K u := by
  by_cases hc : c = 0
  · subst hc
    simpa using GlobalTheory.CompanionTheory.FamClP.hint_zero K
  · have hs : rStab (fun z => c * u z) = rStab u := by
      ext r
      rw [GlobalTheory.CompanionTheory.FamClP.mem_rStab', GlobalTheory.CompanionTheory.FamClP.mem_rStab']
      exact forall_congr' fun x => mul_right_inj' hc
    unfold hint
    rw [hs, mul_left_comm]
    congr 1
    have := smul_finsum c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)
    simpa [smul_eq_mul] using this.symm

theorem hint_swap {H₁ H₂ : Type} [Group H₁] [Group H₂] (A₁ L₁ : Subgroup H₁) (A₂ L₂ : Subgroup H₂)
    (h₁ : L₁ ≤ A₁) (h₂ : L₂ ≤ A₂) (f₁ : L₁.relIndex A₁ ≠ 0) (f₂ : L₂.relIndex A₂ ≠ 0) (u : H₁ → H₂ → ℂ)
    (s₁ : ∀ y, L₁ ≤ rStab (fun x => u x y)) (s₂ : ∀ x, L₂ ≤ rStab (u x))
    (T₁ : Finset (H₁ ⧸ L₁)) (T₂ : Finset (H₂ ⧸ L₂))
    (hT : ∀ x y, u x y ≠ 0 → (x : H₁ ⧸ L₁) ∈ T₁ ∧ (y : H₂ ⧸ L₂) ∈ T₂) :
    hint A₁ (fun x => hint A₂ (u x)) = hint A₂ (fun y => hint A₁ (fun x => u x y)) := by
  have e₁ : ∀ x, hint A₂ (u x) = ((L₂.relIndex A₂ : ℕ) : ℂ)⁻¹ * ∑ q ∈ T₂, u x q.out := by
    intro x
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H₂ A₂ L₂ _ h₂ (s₂ x) f₂, finsum_eq_sum_of_support_subset]
    intro q hq
    have := (hT x q.out hq).2
    simpa using this
  have e₂ : ∀ y, hint A₁ (fun x => u x y) = ((L₁.relIndex A₁ : ℕ) : ℂ)⁻¹ * ∑ q ∈ T₁, u q.out y := by
    intro y
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H₁ A₁ L₁ _ h₁ (s₁ y) f₁, finsum_eq_sum_of_support_subset]
    intro q hq
    have := (hT q.out y hq).1
    simpa using this
  have t₁ : L₁ ≤ rStab (fun x => hint A₂ (u x)) := by
    intro l hl x
    have : u (x * l) = u x := funext fun y => s₁ y hl x
    show hint A₂ (u (x * l)) = hint A₂ (u x)
    rw [this]
  have t₂ : L₂ ≤ rStab (fun y => hint A₁ (fun x => u x y)) := by
    intro l hl y
    have : (fun x => u x (y * l)) = fun x => u x y := funext fun x => s₂ x hl y
    show hint A₁ (fun x => u x (y * l)) = hint A₁ (fun x => u x y)
    rw [this]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H₁ A₁ L₁ _ h₁ t₁ f₁, GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H₂ A₂ L₂ _ h₂ t₂ f₂,
    finsum_eq_sum_of_support_subset (s := T₁), finsum_eq_sum_of_support_subset (s := T₂)]
  · simp only [e₁, e₂, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    ring
  · intro q hq
    obtain ⟨x, hx⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ hq
    have := (hT x q.out hx).2
    simpa using this
  · intro q hq
    obtain ⟨y, hy⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ hq
    have := (hT q.out y hy).1
    simpa using this

theorem hint_conv {H : Type} [CommGroup H] (A L L' : Subgroup H) (hL : L ≤ A) (hL' : L' ≤ A)
    (f : L.relIndex A ≠ 0) (f' : L'.relIndex A ≠ 0) (p q : H → ℂ) (σ : H →* H)
    (sp : L' ≤ rStab p) (sq : L ≤ rStab q) (hσ : ∀ l ∈ L', σ l ∈ L)
    (T : Finset (H ⧸ L)) (T' : Finset (H ⧸ L'))
    (hT : ∀ Y Y', p Y' ≠ 0 → q (Y * (σ Y')⁻¹) ≠ 0 → (Y : H ⧸ L) ∈ T ∧ (Y' : H ⧸ L') ∈ T') :
    hint A (fun Y => hint A (fun Y' => p Y' * q (Y * (σ Y')⁻¹))) = hint A p * hint A q := by
  rw [hint_swap A L A L' hL hL' f f' (fun Y Y' => p Y' * q (Y * (σ Y')⁻¹)) ?_ ?_ T T' ?_]
  · have e : ∀ Y', hint A (fun Y => p Y' * q (Y * (σ Y')⁻¹)) = p Y' * hint A q := by
      intro Y'
      rw [hint_const_mul]
      congr 1
      rw [← GlobalTheory.CompanionTheory.FamClP.hint_left A q (σ Y')⁻¹]
      congr 1
      funext Y
      rw [mul_comm]
    simp only [e]
    simp only [mul_comm _ (hint A q)]
    rw [hint_const_mul]
  · intro Y' l hl Y
    show p Y' * q (Y * l * (σ Y')⁻¹) = p Y' * q (Y * (σ Y')⁻¹)
    rw [show Y * l * (σ Y')⁻¹ = Y * (σ Y')⁻¹ * l by rw [mul_right_comm]]
    rw [sq hl]
  · intro Y l hl Y'
    show p (Y' * l) * q (Y * (σ (Y' * l))⁻¹) = p Y' * q (Y * (σ Y')⁻¹)
    rw [sp hl, map_mul, mul_inv, ← mul_assoc, sq (inv_mem (hσ l hl))]
  · intro Y Y' hu
    exact hT Y Y' (left_ne_zero_of_mul hu) (right_ne_zero_of_mul hu)

theorem finite_out {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    (L : Subgroup H) (K' : Subgroup G) (ho : IsOpen (K' : Set G)) (θ : H → G)
    (hθ : ∀ z z', (θ z)⁻¹ * θ z' ∈ K' → z⁻¹ * z' ∈ L) (C : Set G) (hC : IsCompact C) :
    ∃ T : Finset (H ⧸ L), ∀ z, θ z ∈ C → (z : H ⧸ L) ∈ T := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology ho
  have hfin : ((fun g : G => (g : G ⧸ K')) '' C).Finite :=
    (hC.image continuous_quotient_mk').finite_of_discrete
  let pick : G ⧸ K' → H ⧸ L := fun t =>
    if hx : ∃ z, θ z ∈ C ∧ ((θ z : G) : G ⧸ K') = t then ((hx.choose : H) : H ⧸ L) else ((1 : H) : H ⧸ L)
  refine ⟨hfin.toFinset.image pick, fun z hz => ?_⟩
  refine Finset.mem_image.2 ⟨((θ z : G) : G ⧸ K'), hfin.mem_toFinset.2 ⟨_, hz, rfl⟩, ?_⟩
  have hx : ∃ z', θ z' ∈ C ∧ ((θ z' : G) : G ⧸ K') = ((θ z : G) : G ⧸ K') := ⟨z, hz, rfl⟩
  simp only [pick, dif_pos hx]
  exact QuotientGroup.eq.2 (hθ _ _ (QuotientGroup.eq.1 hx.choose_spec.2))

end Generic

section Local

open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

abbrev NM (a b : ℕ) (w : Pl E) := Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))

def sig (w : Pl E) (k : GLw a w × GLw b w) : NM a b w →* NM a b w :=
  AddMonoidHom.toMultiplicative
    { toFun := fun Y => (k.1⁻¹).val * Y * k.2.val
      map_zero' := by simp
      map_add' := fun Y Z => by simp [Matrix.mul_add, Matrix.add_mul] }

def uLev (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) : Subgroup (NM a b w) :=
  (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)

theorem mem_uLev (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (Y : NM a b w) :
    Y ∈ uLev h w K' ↔ blk h w 1 (Multiplicative.toAdd Y) ∈ K' := Iff.rfl

theorem blk_eq_mul (h : a + b = n) (w : Pl E) (m' k : GLw a w × GLw b w)
    (Y Y' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w (m' * k) Y = blk h w m' Y' * blk h w k (Y - (k.1⁻¹).val * Y' * k.2.val) := by
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simp

theorem unip_conj (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) (l : NM a b w) :
    blk h w 1 (Multiplicative.toAdd (sig w k l)) =
      (blk h w k 0)⁻¹ * blk h w 1 (Multiplicative.toAdd l) * blk h w k 0 := by
  have e : blk h w k 0 * blk h w 1 (Multiplicative.toAdd (sig w k l)) =
      blk h w 1 (Multiplicative.toAdd l) * blk h w k 0 := by
    rw [GlobalTheory.LeviFubini.blk_mul_blk, GlobalTheory.LeviFubini.blk_mul_blk]
    simp [sig]
  rw [mul_assoc, ← e, inv_mul_cancel_left]

theorem stab_unip (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') (f : GLw n w → ℂ)
    (hr : ∀ u ∈ K', ∀ g, f (g * u) = f g) (c d : GLw n w) (hd : d ∈ GlobalTheory.LFun.KGL w n)
    (m : GLw a w × GLw b w) :
    uLev h w K' ≤ rStab (fun Y : NM a b w => f (c * blk h w m (Multiplicative.toAdd Y) * d)) := by
  intro l hl Y
  show f (c * blk h w m (Multiplicative.toAdd (Y * l)) * d) = f (c * blk h w m (Multiplicative.toAdd Y) * d)
  have hU : d⁻¹ * blk h w 1 (Multiplicative.toAdd l) * d ∈ K' := by
    simpa using hN d⁻¹ (inv_mem hd) _ ((mem_uLev h w K' l).1 hl)
  have e : c * blk h w m (Multiplicative.toAdd (Y * l)) * d =
      (c * blk h w m (Multiplicative.toAdd Y) * d) * (d⁻¹ * blk h w 1 (Multiplicative.toAdd l) * d) := by
    rw [GlobalTheory.CompanionTheory.DiagAvg.blk_toAdd_mul]
    group
  rw [e]
  exact hr _ hU _

theorem theta_sep (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (m : GLw a w × GLw b w)
    (z z' : NM a b w)
    (hz : (blk h w m (Multiplicative.toAdd z))⁻¹ * blk h w m (Multiplicative.toAdd z') ∈ K') :
    z⁻¹ * z' ∈ uLev h w K' := by
  rw [mem_uLev]
  have hb : blk h w m (Multiplicative.toAdd z') =
      blk h w m (Multiplicative.toAdd z) * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by
    rw [← GlobalTheory.CompanionTheory.DiagAvg.blk_toAdd_mul, mul_inv_cancel_left]
  rw [hb, inv_mul_cancel_left] at hz
  exact hz

theorem levi_compact (h : a + b = n) (w : Pl E) (C : Set (GLw n w)) (hC : IsCompact C) :
    ∃ D : Set (GLw a w × GLw b w), IsCompact D ∧ ∀ m X, blk h w m X ∈ C → m ∈ D := by
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((CtLevel.blkTL h g.val, MulOpposite.op (CtLevel.blkTL h (g⁻¹).val)),
      (CtLevel.blkBR h g.val, MulOpposite.op (CtLevel.blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((CtLevel.continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((CtLevel.continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, CtLevel.blk_inv, CtLevel.blkTL_blk, CtLevel.blkBR_blk,
      Prod.fst_inv, Prod.snd_inv]
  exact ⟨ι ⁻¹' (ψ '' C), hι.isCompact_preimage (hC.image hψ), fun m X hm => ⟨blk h w m X, hm, (hιψ m X).symm⟩⟩

theorem absHalf_delta_mul (w : Pl E) (m' k : GLw a w × GLw b w) :
    absHalf w ((m' * k).1.val.det ^ b / (m' * k).2.val.det ^ a) =
      absHalf w (m'.1.val.det ^ b / m'.2.val.det ^ a) * absHalf w (k.1.val.det ^ b / k.2.val.det ^ a) := by
  have d : ∀ {c : ℕ} (g : GLw c w), g.val.det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (div_ne_zero (pow_ne_zero _ (d _)) (pow_ne_zero _ (d _)))
    (div_ne_zero (pow_ne_zero _ (d _)) (pow_ne_zero _ (d _)))]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.det_mul, mul_pow]
  rw [mul_div_mul_comm]

def Phi {w : Pl E} (f₁ f₂ : GLw n w → ℂ) (x z B g : GLw n w) : ℂ := f₁ (x⁻¹ * g) * f₂ (g⁻¹ * B * z)

theorem gconv_eq {w : Pl E} (f₁ f₂ : GLw n w → ℂ) (x z B : GLw n w) :
    gconv f₁ f₂ (x⁻¹ * B * z) = hint (GlobalTheory.LFun.KGL w n) (Phi f₁ f₂ x z B) := by
  unfold gconv
  rw [← GlobalTheory.CompanionTheory.FamClP.hint_left _ (fun g => f₁ g * f₂ (g⁻¹ * (x⁻¹ * B * z))) x⁻¹]
  congr 1
  funext g
  show f₁ (x⁻¹ * g) * f₂ ((x⁻¹ * g)⁻¹ * (x⁻¹ * B * z)) = f₁ (x⁻¹ * g) * f₂ (g⁻¹ * B * z)
  congr 2
  group

theorem Phi_right {w : Pl E} (K' : Subgroup (GLw n w)) (f₁ f₂ : GLw n w → ℂ)
    (h₁ : ∀ u ∈ K', ∀ g, f₁ (u * g) = f₁ g ∧ f₁ (g * u) = f₁ g)
    (h₂ : ∀ u ∈ K', ∀ g, f₂ (u * g) = f₂ g ∧ f₂ (g * u) = f₂ g) (x z B g k : GLw n w) (hk : k ∈ K') :
    Phi f₁ f₂ x z B (g * k) = Phi f₁ f₂ x z B g := by
  unfold Phi
  rw [← mul_assoc, (h₁ k hk _).2, show (g * k)⁻¹ * B * z = k⁻¹ * (g⁻¹ * B * z) by group,
    (h₂ k⁻¹ (inv_mem hk) _).1]

theorem Phi_compact {w : Pl E} (f₁ f₂ : GLw n w → ℂ) (hc : HasCompactSupport f₁) (x z B : GLw n w) :
    HasCompactSupport (Phi f₁ f₂ x z B) := by
  refine HasCompactSupport.intro (K := ({x} : Set (GLw n w)) * tsupport f₁) (isCompact_singleton.mul hc) ?_
  intro g hg
  unfold Phi
  have : f₁ (x⁻¹ * g) = 0 := by
    by_contra hne
    exact hg (Set.mem_mul.2 ⟨x, rfl, x⁻¹ * g, subset_tsupport _ hne, by group⟩)
  rw [this, zero_mul]

theorem Phi_supp {w : Pl E} (f₁ f₂ : GLw n w → ℂ) (x y z B c : GLw n w)
    (hne : Phi f₁ f₂ x z B (c * y) ≠ 0) :
    B ∈ ({x} : Set (GLw n w)) * (tsupport f₁ * tsupport f₂) * {z⁻¹} ∧
      c ∈ ({x} : Set (GLw n w)) * tsupport f₁ * {y⁻¹} := by
  have h₁ := subset_tsupport _ (left_ne_zero_of_mul hne)
  have h₂ := subset_tsupport _ (right_ne_zero_of_mul hne)
  constructor
  · have e : B = x * ((x⁻¹ * (c * y)) * ((c * y)⁻¹ * B * z)) * z⁻¹ := by group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul rfl (Set.mul_mem_mul h₁ h₂)) rfl
  · have e : c = x * (x⁻¹ * (c * y)) * y⁻¹ := by group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul rfl h₁) rfl

def Gf (h : a + b = n) (w : Pl E) (f₁ f₂ : GLw n w → ℂ) (x y z : GLw n w) (m m' : GLw a w × GLw b w)
    (Y : NM a b w) : ℂ :=
  hint (intMat a b w) fun Y' : NM a b w =>
    Phi f₁ f₂ x z (blk h w m (Multiplicative.toAdd Y)) (blk h w m' (Multiplicative.toAdd Y') * y)

theorem Gf_stab (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') (f₁ f₂ : GLw n w → ℂ)
    (h₂ : ∀ u ∈ K', ∀ g, f₂ (u * g) = f₂ g ∧ f₂ (g * u) = f₂ g) (x y z : GLw n w)
    (hz : z ∈ GlobalTheory.LFun.KGL w n) (m m' : GLw a w × GLw b w) :
    uLev h w K' ≤ rStab (Gf h w f₁ f₂ x y z m m') := by
  intro l hl Y
  show hint _ _ = hint _ _
  congr 1
  funext Y'
  unfold Phi
  congr 1
  exact stab_unip h w K' hN f₂ (fun u hu g => (h₂ u hu g).2) _ z hz m hl Y

def mLev (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) : Subgroup (GLw a w × GLw b w) :=
  K'.comap (CtLevel.dgM h w)

theorem levi_stab (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (hKK : K' ≤ GlobalTheory.LFun.KGL w n)
    (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') (Φ : GLw n w → ℂ)
    (hΦ : ∀ g k, k ∈ K' → Φ (g * k) = Φ g) (y : GLw n w) (hy : y ∈ GlobalTheory.LFun.KGL w n) :
    mLev h w K' ≤ rStab (fun m' : GLw a w × GLw b w => hint (intMat a b w) fun Y' : NM a b w =>
      Φ (blk h w m' (Multiplicative.toAdd Y') * y)) := by
  intro k hk m'
  have hk' : CtLevel.dgM h w k ∈ K' := hk
  show hint (intMat a b w) (fun Y' : NM a b w => Φ (blk h w (m' * k) (Multiplicative.toAdd Y') * y)) =
    hint (intMat a b w) fun Y' : NM a b w => Φ (blk h w m' (Multiplicative.toAdd Y') * y)
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blocks_mem_KGL h w k (hKK hk')
  have e : (fun Y' : NM a b w => Φ (blk h w (m' * k) (Multiplicative.toAdd Y') * y)) =
      fun Y' => (fun Y'' : NM a b w => Φ (blk h w m' (Multiplicative.toAdd Y'') * y))
        (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd Y' * (k.2⁻¹).val)) := by
    funext Y'
    rw [(CtLevel.blk_mul_dgM E a b n h w m' k _).2]
    have hc : y⁻¹ * CtLevel.dgM h w k * y ∈ K' := by
      simpa using hN y⁻¹ (inv_mem hy) _ hk'
    have e2 : blk h w m' (k.1.val * Multiplicative.toAdd Y' * (k.2⁻¹).val) * CtLevel.dgM h w k * y =
        (blk h w m' (k.1.val * Multiplicative.toAdd Y' * (k.2⁻¹).val) * y) * (y⁻¹ * CtLevel.dgM h w k * y) := by
      group
    rw [e2, hΦ _ _ hc]
    rfl
  rw [e]
  exact HintInv.hint_intMat_mul_mul E a b w (fun Y'' : NM a b w => Φ (blk h w m' (Multiplicative.toAdd Y'') * y))
    k.1 k.2⁻¹ h1 (inv_mem h2)

theorem Gf_conv (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (hKo : IsOpen (K' : Set (GLw n w)))
    (hKK : K' ≤ GlobalTheory.LFun.KGL w n) (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f₁ f₂ : GLw n w → ℂ) (h₁ : ∀ u ∈ K', ∀ g, f₁ (u * g) = f₁ g ∧ f₁ (g * u) = f₁ g)
    (h₂ : ∀ u ∈ K', ∀ g, f₂ (u * g) = f₂ g ∧ f₂ (g * u) = f₂ g)
    (c₁ : HasCompactSupport f₁) (c₂ : HasCompactSupport f₂) (x y z : GLw n w)
    (hy : y ∈ GlobalTheory.LFun.KGL w n) (hz : z ∈ GlobalTheory.LFun.KGL w n) (m m' : GLw a w × GLw b w) :
    hint (intMat a b w) (Gf h w f₁ f₂ x y z m m') =
      hint (intMat a b w) (fun Y : NM a b w => f₁ (x⁻¹ * blk h w m' (Multiplicative.toAdd Y) * y)) *
      hint (intMat a b w) (fun Y : NM a b w => f₂ (y⁻¹ * blk h w (m'⁻¹ * m) (Multiplicative.toAdd Y) * z)) := by
  set k := m'⁻¹ * m with hk
  set D := blk h w k 0 with hD
  set K₂ : Subgroup (GLw n w) := K' ⊓ K'.comap (MulAut.conj D⁻¹).toMonoidHom with hK₂
  have hK₂o : IsOpen (K₂ : Set (GLw n w)) := by
    rw [hK₂, Subgroup.coe_inf]
    refine hKo.inter ?_
    have : Continuous (fun g : GLw n w => D⁻¹ * g * D⁻¹⁻¹) := (continuous_const.mul continuous_id).mul continuous_const
    exact hKo.preimage this
  have hK₂K : K₂ ≤ K' := inf_le_left
  obtain ⟨hLA, hfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hKo hKK
  obtain ⟨hLA', hfin'⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K₂ hK₂o (hK₂K.trans hKK)
  have hLL : uLev h w K₂ ≤ uLev h w K' := fun l hl => hK₂K hl
  have hσ : ∀ l ∈ uLev h w K₂, sig w k l ∈ uLev h w K' := by
    intro l hl
    rw [mem_uLev, unip_conj]
    have : blk h w 1 (Multiplicative.toAdd l) ∈ K₂ := hl
    have h3 := this.2
    simpa [MulAut.conj_apply] using h3
  obtain ⟨T, hT⟩ := finite_out (uLev h w K') K' hKo (fun Y : NM a b w => blk h w m (Multiplicative.toAdd Y))
    (theta_sep h w K' m) (({x} : Set (GLw n w)) * (tsupport f₁ * tsupport f₂) * {z⁻¹})
    ((isCompact_singleton.mul (IsCompact.mul c₁ c₂)).mul isCompact_singleton)
  obtain ⟨T', hT'⟩ := finite_out (uLev h w K₂) K₂ hK₂o (fun Y : NM a b w => blk h w m' (Multiplicative.toAdd Y))
    (theta_sep h w K₂ m') (({x} : Set (GLw n w)) * tsupport f₁ * {y⁻¹})
    ((isCompact_singleton.mul c₁).mul isCompact_singleton)
  have key : ∀ Y Y' : NM a b w,
      Phi f₁ f₂ x z (blk h w m (Multiplicative.toAdd Y)) (blk h w m' (Multiplicative.toAdd Y') * y) =
      f₁ (x⁻¹ * blk h w m' (Multiplicative.toAdd Y') * y) *
        f₂ (y⁻¹ * blk h w k (Multiplicative.toAdd (Y * (sig w k Y')⁻¹)) * z) := by
    intro Y Y'
    have e : blk h w m (Multiplicative.toAdd Y) = blk h w m' (Multiplicative.toAdd Y') *
        blk h w k (Multiplicative.toAdd (Y * (sig w k Y')⁻¹)) := by
      have := blk_eq_mul h w m' k (Multiplicative.toAdd Y) (Multiplicative.toAdd Y')
      rw [hk, mul_inv_cancel_left] at this
      rw [this, hk]
      congr 2
      simp [sig, sub_eq_add_neg]
    unfold Phi
    rw [e, ← mul_assoc x⁻¹]
    congr 2
    group
  have hG : Gf h w f₁ f₂ x y z m m' = fun Y => hint (intMat a b w) fun Y' : NM a b w =>
      f₁ (x⁻¹ * blk h w m' (Multiplicative.toAdd Y') * y) *
        f₂ (y⁻¹ * blk h w k (Multiplicative.toAdd (Y * (sig w k Y')⁻¹)) * z) := by
    funext Y
    unfold Gf
    congr 1
    funext Y'
    exact key Y Y'
  rw [hG]
  refine hint_conv (intMat a b w) (uLev h w K') (uLev h w K₂) hLA hLA' hfin hfin'
    (fun Y : NM a b w => f₁ (x⁻¹ * blk h w m' (Multiplicative.toAdd Y) * y))
    (fun Y : NM a b w => f₂ (y⁻¹ * blk h w k (Multiplicative.toAdd Y) * z)) (sig w k)
    (hLL.trans (stab_unip h w K' hN f₁ (fun u hu g => (h₁ u hu g).2) _ y hy m'))
    (stab_unip h w K' hN f₂ (fun u hu g => (h₂ u hu g).2) _ z hz k) hσ T T' ?_
  intro Y Y' hp hq
  have hne : Phi f₁ f₂ x z (blk h w m (Multiplicative.toAdd Y)) (blk h w m' (Multiplicative.toAdd Y') * y) ≠ 0 := by
    rw [key]
    exact mul_ne_zero hp hq
  obtain ⟨s₁, s₂⟩ := Phi_supp f₁ f₂ x y z _ _ hne
  exact ⟨hT Y s₁, hT' Y' s₂⟩

theorem mLev_open (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (hKo : IsOpen (K' : Set (GLw n w))) :
    IsOpen (mLev h w K' : Set (GLw a w × GLw b w)) :=
  hKo.preimage (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.continuous_dgM h w)

theorem mLev_le (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (hKK : K' ≤ GlobalTheory.LFun.KGL w n) :
    mLev h w K' ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := fun k hk =>
  Subgroup.mem_prod.2 (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blocks_mem_KGL h w k (hKK hk))

theorem mLev_index (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (hKo : IsOpen (K' : Set (GLw n w))) :
    (mLev h w K').relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 := by
  refine GlobalTheory.CompanionTheory.SplitConvHecke.relIndex_ne_zero_of_isOpen _ _ (mLev_open h w K' hKo) ?_
  rw [Subgroup.coe_prod]
  exact (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)

theorem conv_entry (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (hKo : IsOpen (K' : Set (GLw n w)))
    (hKK : K' ≤ GlobalTheory.LFun.KGL w n) (hN : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f₁ f₂ : GLw n w → ℂ) (h₁ : ∀ u ∈ K', ∀ g, f₁ (u * g) = f₁ g ∧ f₁ (g * u) = f₁ g)
    (h₂ : ∀ u ∈ K', ∀ g, f₂ (u * g) = f₂ g ∧ f₂ (g * u) = f₂ g)
    (c₁ : HasCompactSupport f₁) (c₂ : HasCompactSupport f₂) (x y z : GLw n w)
    (hy : y ∈ GlobalTheory.LFun.KGL w n) (hz : z ∈ GlobalTheory.LFun.KGL w n) (m : GLw a w × GLw b w)
    (T : Finset (NM a b w ⧸ uLev h w K'))
    (hT : ∀ Y : NM a b w, blk h w m (Multiplicative.toAdd Y) ∈
      ({x} : Set (GLw n w)) * (tsupport f₁ * tsupport f₂) * {z⁻¹} → (Y : NM a b w ⧸ uLev h w K') ∈ T) :
    absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
      hint (intMat a b w) (fun Y : NM a b w => hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
        fun m' => Gf h w f₁ f₂ x y z m m' Y) =
      mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m := by
  obtain ⟨hLA, hfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hKo hKK
  obtain ⟨D₁, hD₁, hD⟩ := levi_compact (a := a) (b := b) h w (({x} : Set (GLw n w)) * tsupport f₁ * {y⁻¹})
    ((isCompact_singleton.mul c₁).mul isCompact_singleton)
  obtain ⟨T₂, hT₂⟩ := finite_out (mLev h w K') (mLev h w K') (mLev_open h w K' hKo) id
    (fun _ _ hz => hz) D₁ hD₁
  have hsw := hint_swap (intMat a b w) (uLev h w K') ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (mLev h w K')
    hLA (mLev_le h w K' hKK) hfin (mLev_index h w K' hKo)
    (fun (Y : NM a b w) m' => Gf h w f₁ f₂ x y z m m' Y)
    (fun m' => Gf_stab h w K' hN f₁ f₂ h₂ x y z hz m m')
    (fun Y => levi_stab h w K' hKK hN _ (fun g k hk => Phi_right K' f₁ f₂ h₁ h₂ x z _ g k hk) y hy)
    T T₂ (by
      intro Y m' hne
      obtain ⟨Y', hY'⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ hne
      obtain ⟨s₁, s₂⟩ := Phi_supp f₁ f₂ x y z _ _ hY'
      exact ⟨hT Y s₁, hT₂ m' (hD m' _ s₂)⟩)
  rw [hsw]
  simp only [fun m' => Gf_conv h w K' hKo hKK hN f₁ f₂ h₁ h₂ c₁ c₂ x y z hy hz m m']
  rw [← hint_const_mul]
  unfold mconv
  congr 1
  funext m'
  have e := absHalf_delta_mul w m' (m'⁻¹ * m)
  rw [mul_inv_cancel_left] at e
  unfold phi3
  rw [e]
  ring

theorem constant_term_convolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f₁ f₂ : GLw n w → ℂ, IsHk K' f₁ → IsHk K' f₂ → ∀ x ∈ X, ∀ z ∈ X, ∀ m, phi3 h w (gconv f₁ f₂) x z m = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m := by
  intro E _ _ _ n a b h w K' hKo hKK hN X hXK hX f₁ f₂ hf₁ hf₂ x hx z hz m
  have h₁ : ∀ u ∈ K', ∀ g, f₁ (u * g) = f₁ g ∧ f₁ (g * u) = f₁ g := fun u hu g =>
    ⟨by simpa using hf₁.2.2.2 u hu 1 K'.one_mem g, by simpa using hf₁.2.2.2 1 K'.one_mem u hu g⟩
  have h₂ : ∀ u ∈ K', ∀ g, f₂ (u * g) = f₂ g ∧ f₂ (g * u) = f₂ g := fun u hu g =>
    ⟨by simpa using hf₂.2.2.2 u hu 1 K'.one_mem g, by simpa using hf₂.2.2.2 1 K'.one_mem u hu g⟩
  have c₁ := hf₁.2.2.1
  have c₂ := hf₂.2.2.1
  have hzK := hXK z hz
  obtain ⟨hLA, hfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hKo hKK
  obtain ⟨T, hT⟩ := finite_out (uLev h w K') K' hKo (fun Y : NM a b w => blk h w m (Multiplicative.toAdd Y))
    (theta_sep h w K' m) (({x} : Set (GLw n w)) * (tsupport f₁ * tsupport f₂) * {z⁻¹})
    ((isCompact_singleton.mul (IsCompact.mul c₁ c₂)).mul isCompact_singleton)
  let v : GLw n w → NM a b w → ℂ := fun y Y => hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
    fun m' => Gf h w f₁ f₂ x y z m m' Y
  have step : ∀ Y : NM a b w, gconv f₁ f₂ (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * z) =
      ((X.card : ℂ))⁻¹ * ∑ y ∈ X, v y Y := by
    intro Y
    rw [gconv_eq]
    exact GlobalTheory.CompanionTheory.IntDec.integral_decomposition E n a b h w K' hKo hKK hN X hXK hX _
      (fun g k hk => Phi_right K' f₁ f₂ h₁ h₂ x z _ g k hk) (Phi_compact f₁ f₂ c₁ x z _)
  have hst : ∀ y ∈ X, uLev h w K' ≤ rStab (v y) := by
    intro y _ l hl Y
    have e : (fun m' => Gf h w f₁ f₂ x y z m m' (Y * l)) = fun m' => Gf h w f₁ f₂ x y z m m' Y :=
      funext fun m' => Gf_stab h w K' hN f₁ f₂ h₂ x y z hzK m m' hl Y
    exact congrArg (hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))) e
  have hsupp : ∀ y ∈ X, (Function.support fun q : NM a b w ⧸ uLev h w K' => v y q.out).Finite := by
    intro y _
    refine T.finite_toSet.subset fun q hq => ?_
    obtain ⟨m', hm'⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ hq
    obtain ⟨Y', hY'⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ hm'
    have := hT q.out (Phi_supp f₁ f₂ x y z _ _ hY').1
    simpa using this
  show absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) (fun Y : NM a b w =>
    gconv f₁ f₂ (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * z)) = _
  simp only [step]
  rw [GlobalTheory.CompanionTheory.DiagAvg.hint_const_mul_sum (intMat a b w) (uLev h w K') hLA hfin X v _ hst hsupp]
  have e : ∀ y ∈ X, mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) (v y) := fun y hy =>
    (conv_entry h w K' hKo hKK hN f₁ f₂ h₁ h₂ c₁ c₂ x y z (hXK y hy) hzK m T hT).symm
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  ring

end Local

end GlobalTheory.CompanionTheory.ConvMat
