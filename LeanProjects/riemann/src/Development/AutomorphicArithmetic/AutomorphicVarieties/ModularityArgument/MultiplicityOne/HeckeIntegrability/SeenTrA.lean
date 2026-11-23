import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun GlobalTheory.PRep

private theorem hint_fst {G P : Type} [Group G] [Group P] [Subsingleton P] (K N : Subgroup G) (K' : Subgroup P)
    (u : G × P → ℂ) (hNK : N ≤ K) (hu : ∀ k ∈ N, ∀ x, u (x * k, 1) = u (x, 1)) (hi : N.relIndex K ≠ 0) :
    hint (K.prod K') u = ((N.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ N, u (q.out, 1) := by
  have hp : ∀ z : G × P, z = (z.1, 1) := fun z => Prod.ext rfl (Subsingleton.elim _ _)
  set L : Subgroup (G × P) := N.comap (MonoidHom.fst G P) with hL
  have hmap : (K.prod K').map (MonoidHom.fst G P) = K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hx
      exact ⟨(x, 1), ⟨hx, K'.one_mem⟩, rfl⟩
  have hrel : L.relIndex (K.prod K') = N.relIndex K := by
    rw [hL, Subgroup.relIndex_comap, hmap]
  have hLK : L ≤ K.prod K' := fun z hz => by
    rw [hp z]
    exact ⟨hNK hz, K'.one_mem⟩
  have hLu : L ≤ rStab u := fun k hk x => by
    have h1 : x * k = (x.1 * k.1, 1) := Prod.ext rfl (Subsingleton.elim _ _)
    rw [h1, hu k.1 hk x.1, ← hp x]
  rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ _ L u hLK hLu (by rwa [hrel]), hrel]
  congr 1
  have hval : ∀ q : G ⧸ N, u (Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) = u (q.out, 1) := by
    intro q
    have hm : ((q.out, (1 : P)))⁻¹ * Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) ∈ L :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
    obtain ⟨k, hk⟩ : ∃ k : G × P, k ∈ L ∧ Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) = (q.out, 1) * k :=
      ⟨_, hm, (mul_inv_cancel_left _ _).symm⟩
    rw [hk.2]
    exact hLu hk.1 _
  have hbij : Function.Bijective (fun q : G ⧸ N => (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) := by
    constructor
    · intro a b hab
      have h := QuotientGroup.eq.mp hab
      have h2 : (a.out)⁻¹ * b.out ∈ N := by simpa [hL] using h
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      exact QuotientGroup.eq.mpr h2
    · intro c
      induction c using QuotientGroup.induction_on with
      | H z =>
        refine ⟨QuotientGroup.mk z.1, QuotientGroup.eq.mpr ?_⟩
        have h3 : ((QuotientGroup.mk z.1 : G ⧸ N).out)⁻¹ * z.1 ∈ N :=
          QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
        simpa [hL] using h3
  rw [← finsum_comp _ hbij]
  exact finsum_congr hval

private theorem tr_core (hTr : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel) (hCv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp)
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K N : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hNo : IsOpen (N : Set G)) (hNc : IsCompact (N : Set G)) (hNK : N ≤ K)
    (hi : ((N.relIndex K : ℕ) : ℂ) ≠ 0) (hfd : FiniteDimensional ℂ (fixed ρ N))
    (f₁ f₂ F : G → ℂ) (h₁ : IsHecke N f₁) (h₂ : IsHecke N f₂)
    (hFeq : F = fun g => ((N.relIndex K : ℕ) : ℂ)⁻¹ * UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂ g) :
    trOn (fixed ρ N) (Lv ρ N f₁ * Lv ρ N f₂) = ((N.relIndex K : ℕ) : ℂ) ^ 2 * trc ρ K F := by
  set i : ℂ := ((N.relIndex K : ℕ) : ℂ) with hidef
  have hcvH : IsHecke N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) :=
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cvHecke _ N hNo hNc f₁ f₂ h₁ h₂
  have hFH : IsHecke N F := by
    refine ⟨?_, ?_⟩
    · rw [hFeq]
      exact hcvH.1.mul_left (f := fun _ => i⁻¹)
    · intro k hk x
      rw [hFeq]
      simp only
      rw [(hcvH.2 k hk x).1, (hcvH.2 k hk x).2]
      exact ⟨rfl, rfl⟩
  have hNK₁ : N ≤ K ⊓ rStab F ⊓ rStab fun y => F y⁻¹ := by
    refine le_inf (le_inf hNK ?_) ?_
    · exact fun k hk x => (hFH.2 k hk x).2
    · intro k hk x
      have e : (x * k)⁻¹ = k⁻¹ * x⁻¹ := by group
      show F (x * k)⁻¹ = F x⁻¹
      rw [e]
      exact (hFH.2 k⁻¹ (N.inv_mem hk) _).1
  have hK₁H : IsHecke (K ⊓ rStab F ⊓ rStab fun y => F y⁻¹) F := by
    refine ⟨hFH.1, fun k hk x => ⟨?_, hk.1.2 x⟩⟩
    have hk' : k⁻¹ ∈ rStab fun y => F y⁻¹ := (rStab _).inv_mem hk.2
    have := hk' x⁻¹
    simpa using this
  have hlev := hTr G K hKo hKc V ρ F _ N hNo hNK₁ (inf_le_left.trans inf_le_left) hK₁H hfd
  have hop : levOp ρ K N F LinearMap.id = i⁻¹ • i⁻¹ • levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id := by
    rw [hFeq]
    unfold levOp
    rw [Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    congr 1
    rw [smul_finsum]
    exact finsum_congr fun q => by rw [mul_smul]
  have hmul : ∀ v ∈ fixed ρ N, levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id v = (Lv ρ N f₁ * Lv ρ N f₂) v :=
    fun v hv => (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).1
  have hpres : ∀ v ∈ fixed ρ N, (Lv ρ N f₁ * Lv ρ N f₂) v ∈ fixed ρ N := fun v hv =>
    (hCv G N hNo hNc V ρ f₂ f₁ h₂ h₁ _ (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).2.1).2.1
  have hstab : ∀ v ∈ fixed ρ N, levOp ρ K N F LinearMap.id v ∈ fixed ρ N := fun v hv => by
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v hv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hpres v hv))
  have hres : (levOp ρ K N F LinearMap.id).restrict hstab = (i⁻¹ * i⁻¹) • (Lv ρ N f₁ * Lv ρ N f₂).restrict hpres := by
    ext v
    simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Submodule.coe_smul]
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v v.2, mul_smul]
  unfold trc
  rw [← hlev]
  unfold twTr trOn
  rw [dif_pos hstab, dif_pos hpres, hres, map_smul, smul_eq_mul]
  field_simp

theorem UpperTheory.V.Z.Mult.Pi.seenTrA :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → UpperTheory.V.Z.Mult.Pi.SeenTrA := by
  intro hTr hAdm hCv E _ _ _ n w hw τ N hNo hNK
  obtain ⟨-, -, hKo, hKc, -⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w
  have hNc : IsCompact (N : Set (GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK
  haveI : Finite ((KGL w n : Subgroup (GLw n w)) ⧸ N.subgroupOf (KGL w n)) :=
    GlobalTheory.TwTrLevel.finite_quot (KGL w n) (KGL w n) N hKc hKo hNo le_rfl
  have hi : N.relIndex (KGL w n) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hiC : ((N.relIndex (KGL w n) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  intro φ₁ φ₂ hb
  refine tr_core hTr hCv τ.ρ (KGL w n) N hKo hKc hNo hNc hNK hiC (hAdm E n w τ N hNo) _ _ _ (hb false) (hb true) ?_
  funext g
  have h₁ := hb false
  have h₂ := hb true
  have hr : ∀ k ∈ N, ∀ x : GLw n w, two φ₁ φ₂ w false (x * k) * two φ₁ φ₂ w true ((x * k)⁻¹ * g) =
      two φ₁ φ₂ w false x * two φ₁ φ₂ w true (x⁻¹ * g) := by
    intro k hk x
    have e : (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) := by group
    rw [e, (h₁.2 k hk x).2, (h₂.2 k⁻¹ (N.inv_mem hk) _).1]
  have hcv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N (two φ₁ φ₂ w false) (two φ₁ φ₂ w true) g =
      ∑ᶠ q : GLw n w ⧸ N, two φ₁ φ₂ w false q.out * two φ₁ φ₂ w true (q.out⁻¹ * g) := by
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv
    rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ N N _ le_rfl (fun k hk x => hr k hk x) (by simp)]
    simp
  have hpr : ∀ x : GLw n w, ((x, 1) : GLw n w × GLw 0 w)⁻¹ * (g, 1) = (x⁻¹ * g, 1) := fun x =>
    Prod.ext rfl (Subsingleton.elim _ _)
  rw [hcv]
  unfold PositivityTheory.Rg.BcB.G8.seen
  rw [if_pos hw]
  rw [hint_fst (KGL w n) N (KGL w 0) _ hNK ?_ hi]
  · congr 1
    refine finsum_congr fun q => ?_
    rw [hpr]
    rfl
  · intro k hk x
    rw [hpr, hpr]
    exact hr k hk x
