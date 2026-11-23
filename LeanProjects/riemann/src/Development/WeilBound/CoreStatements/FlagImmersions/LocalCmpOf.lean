import Development.WeilBound.CoreStatements.FlagImmersions.LogDetBounds
import Development.WeilBound.CoreStatements.FlagImmersions.FrameOfMatrix
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

open Loc

set_option maxHeartbeats 1600000 in
theorem localCmp_of : PointEx → ValuePhi → IntFrames → FibSandwich → LocalCmp := by
  intro hPt hVal hInt hFib E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 Fl τ i j a b a' b' d₁ d₂ φ F' _ _ ι ψ p κ' π m k
    t hgp hT hφ hgen hrep ha' hb' hd₁ hd₂ ea eb ha0 hb0 hψ hπ hm hord hfin
  obtain ⟨V, L, _, _, _, _, _, _, _, jL, ψL, z, hj, hjψ, hint, hval, hreg⟩ :=
    hPt E H D l Xo c Y U Z S Ω K J y 𝔐 F' ψ p κ' hgp
  have hξ := 𝔐.tie.gen
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hκ' : ∀ u, κ' u = jL (ψL u) := fun u => (DFunLike.congr_fun hjψ u).symm
  have hcst : ∀ u, 𝔐.cst u = ψ (ι u) := fun u => (DFunLike.congr_fun hψ u).symm
  obtain ⟨evV, hevV⟩ := exists_ev hξ z (𝔐.all _)
  obtain ⟨evL, hevL⟩ := exists_ev hξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (𝔐.all _)
  obtain ⟨jV, hjVe⟩ : ∃ jV : V →+* ℂ_[p], ∀ a, jV a = jL (algebraMap V L a) := ⟨jL.comp (algebraMap V L), fun _ => rfl⟩
  have hjV : ∀ a, ‖jV a‖ ≤ 1 := fun a => by rw [hjVe]; exact (hj _).2 ⟨a, rfl⟩
  have hjV0 : ∀ a, a ≠ 0 → jV a ≠ 0 := fun a ha => by
    rw [hjVe]
    exact (map_ne_zero jL).2 ((map_ne_zero_iff _ (IsFractionRing.injective V L)).2 ha)

  have hfr : ∀ s, ∃ bb : Fin (labelRk D s) → 𝔐.Li, flagStep Ω bb (labelRk D s) = flagStep Ω (Fl.b s) (labelRk D s) ∧
      (𝔐.V s).IsFrameAt bb ⟨centre z, 𝔐.all _⟩ ∧ (𝔐.V s).IsFrameAt bb ⟨centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z), 𝔐.all _⟩ := fun s => by
    obtain ⟨W, hW, bb, h1, h2⟩ := Fl.sub s ⟨centre z, 𝔐.all _⟩ trivial
    exact ⟨bb, h1 _, h2 _ trivial hW, h2 _ trivial ((LieTangent.centre_specializes _ z).mem_open W.isOpen hW)⟩
  have hex : ∀ s (bb : Fin (labelRk D s) → 𝔐.Li), (𝔐.V s).IsFrameAt bb ⟨centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z), 𝔐.all _⟩ →
      ∀ k, ∃ w, 𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (bb k) w := fun s bb hb k => by
    have h1 : 𝔐.V s ⟨centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z), 𝔐.all _⟩ = 𝔐.dR s ⟨centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z), 𝔐.all _⟩ := by
      refine Lat.patch_of_not S _ _ fun r hr hf => hf ?_
      have h2 : ValAt 𝔐.ξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (r : Ω) (r : L) := by simpa using hevL (r : _)
      exact unit_of_val _ h2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (𝔐.S_prime r hr).ne_zero))
    have h3 : bb k ∈ 𝔐.dR s ⟨centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z), 𝔐.all _⟩ := by
      rw [← h1, hb.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact (𝔐.M.exists_valAt_iff _ _).2 ⟨𝔐.all _, h3.1⟩
  obtain ⟨bp, hp1, hp2, hp3⟩ := hfr (.inl τ)
  obtain ⟨bq, hq1, hq2, hq3⟩ := hfr (.inr τ)
  choose vp hvp using hex _ bp hp3
  choose vq hvq using hex _ bq hq3

  have hint' : ∀ s (a : 𝓞 E), ‖κ' (ι (labelEmb c s a))‖ ≤ 1 := fun s a => by
    rw [hκ']
    have h1 : IsIntegral ℤ (ψL (ι (labelEmb c s a))) :=
      map_isIntegral_int ((ψL.comp ι).comp (labelEmb c s)) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := V))
    exact (hj _).2 ⟨v, hv⟩
  have hembR : ∀ s (a : 𝓞 E), 𝔐.emb s a ∈ regAt 𝔐.ξ ⟨centre z, 𝔐.all _⟩ := fun s a => by
    have h1 : 𝔐.emb s a = ψ (ι (labelEmb c s a)) := hcst _
    rw [h1]
    exact hreg _ (hint' s a)
  obtain ⟨σ, hσ⟩ : ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* V), ∀ s a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ s a) :=
    ⟨fun s => evV.comp ((𝔐.emb s).codRestrict _ (hembR s)), fun s a => hevV ⟨_, hembR s a⟩⟩
  have hcv : ∀ x : c.F, ValAt 𝔐.ξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (𝔐.cst x) ((ψL.comp ι) x) := fun x => by
    rw [hcst]
    exact hval _
  have hσL : ∀ s, (algebraMap V L).comp (σ s) = (ψL.comp ι).comp (labelEmb c s) := fun s =>
    RingHom.ext fun a => LieTangent.valAt_unique hξ (LieTangent.valAt_base hξ (algebraMap V L) (hσ s a)) (hcv _)
  have hσp : (algebraMap V L).comp (σ (.inl τ)) = (ψL.comp ι).comp (tauIn c τ.1) := hσL _
  have hσq : (algebraMap V L).comp (σ (.inr τ)) = (ψL.comp ι).comp (tauIn c (ComplexEmbedding.conjugate τ.1)) := by
    rw [hσL, CptStalk.labelEmb_inr]

  obtain ⟨α₀, hα⟩ := wedge_of_span bp (Fl.b (.inl τ)) hp1
  obtain ⟨β₀, hβ⟩ := wedge_of_span bq (Fl.b (.inr τ)) hq1
  have ea' : a' = (d₁ * α₀) • exteriorPower.ιMulti Ω D.p bp := by
    rw [mul_smul]
    exact ea.trans (congrArg (d₁ • ·) hα)
  have eb' : b' = (d₂ * β₀) • exteriorPower.ιMulti Ω D.q bq := by
    rw [mul_smul]
    exact eb.trans (congrArg (d₂ • ·) hβ)
  have hα0 : α₀ ≠ 0 := fun h => ha0 (ea'.trans (by rw [h, mul_zero, zero_smul]))
  have hβ0 : β₀ ≠ 0 := fun h => hb0 (eb'.trans (by rw [h, mul_zero, zero_smul]))
  have hu := coeff_order hp2 hq2 hα0 hβ0 hα hβ (hord ⟨centre z, 𝔐.all _⟩ hreg)
  have ecc : d₁ / d₂ * α₀ / β₀ = d₁ * α₀ / (d₂ * β₀) := by field_simp
  rw [ecc] at hu
  generalize hcc : d₁ * α₀ / (d₂ * β₀) = cc at hu
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hw1 : ‖jV (evV ⟨_, hu1⟩)‖ = 1 := by
    have e1 : jV (evV ⟨_, hu1⟩) * jV (evV ⟨_, hu2⟩) = 1 := by
      rw [← map_mul, ← map_mul, ← map_one jV, ← map_one evV]
      congr 2
      exact Subtype.ext (mul_inv_cancel₀ hu0)
    have e2 : ‖jV (evV ⟨_, hu1⟩)‖ * ‖jV (evV ⟨_, hu2⟩)‖ = 1 := by rw [← norm_mul, e1, norm_one]
    have a1 := hjV (evV ⟨_, hu1⟩)
    have a2 := hjV (evV ⟨_, hu2⟩)
    have a3 := norm_nonneg (jV (evV ⟨_, hu1⟩))
    refine le_antisymm a1 ?_
    calc (1 : ℝ) = _ := e2.symm
      _ ≤ ‖jV (evV ⟨_, hu1⟩)‖ * 1 := mul_le_mul_of_nonneg_left a2 a3
      _ = _ := mul_one _
  have hπL : ψL π ≠ 0 := (map_ne_zero ψL).2 hπ
  have hπΩ : ψ π ^ k ≠ 0 := zpow_ne_zero _ ((map_ne_zero ψ).2 hπ)
  have hvm : ValAt 𝔐.ξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (cc ^ m) (algebraMap V L (evV ⟨_, hu1⟩) * ψL π ^ k) := by
    have := val_mul (LieTangent.valAt_base hξ (algebraMap V L) (hevV ⟨_, hu1⟩)) (val_zpow (hval π) hπL k)
    rwa [show ((⟨_, hu1⟩ : regAt 𝔐.ξ ⟨centre z, 𝔐.all _⟩) : Ω) = cc ^ m / ψ π ^ k from rfl, div_mul_cancel₀ _ hπΩ] at this
  have hccR : cc ∈ regAt 𝔐.ξ ⟨centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z), 𝔐.all _⟩ := by
    refine hN _ cc (IsIntegral.of_pow hm ?_)
    obtain ⟨_, s₀, hs₀, -⟩ := hvm
    exact isIntegral_algebraMap (R := regAt 𝔐.ξ ⟨centre (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z), 𝔐.all _⟩) (x := ⟨cc ^ m, s₀, hs₀⟩)
  obtain ⟨uL, huL⟩ : ∃ uL : L, ValAt 𝔐.ξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) cc uL := ⟨_, hevL ⟨cc, hccR⟩⟩
  have hpow : uL ^ m = algebraMap V L (evV ⟨_, hu1⟩) * ψL π ^ k := LieTangent.valAt_unique hξ (val_pow huL m) hvm
  have hnorm : ‖jL uL‖ ^ m = ‖κ' π‖ ^ k := by
    rw [← norm_pow, ← map_pow, hpow, map_mul, ← hjVe, norm_mul, hw1, one_mul, map_zpow₀, norm_zpow, hκ']
  have hlog : (k : ℝ) / m * Real.log ‖κ' π‖ = Real.log ‖jL uL‖ := by
    have h1 := congrArg Real.log hnorm
    rw [Real.log_pow, Real.log_zpow] at h1
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    field_simp
    linarith
  rw [hlog]

  obtain ⟨y₀, v, w, hz, hF, hφu, tp, tq⟩ := hVal E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j a b a' b' φ L (ψL.comp ι) (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z)
    bp bq vp vq (d₁ * α₀) (d₂ * β₀) uL hT hφ hgen hrep ha' hb' hint hcv hp3 hq3 hvp hvq ea' eb' (hcc ▸ huL)
  obtain ⟨T, tK, mm, mm', g, MC, MU, ρC, hMC, hMU, htie, -, hIF⟩ := hInt E H D l Xo c Y S Ω K J y 𝔐 V L z y₀ hz
  obtain ⟨xp, hxp1, hxp2, hxp3⟩ := hFib E H D l Xo c Y S Ω K J y 𝔐 V L p jL z g MC ρC (.inl τ) (σ _) bp hj hMC (hσ _) hp2
  obtain ⟨xq, hxq1, hxq2, hxq3⟩ := hFib E H D l Xo c Y S Ω K J y 𝔐 V L p jL z g MC ρC (.inr τ) (σ _) bq hj hMC (hσ _) hq2
  have hv : v = fun k : Fin D.p => MU.pt (xp k) := funext fun k =>
    tied_unique (tp k) ((LieModel.ValAt.unique hξ (hxp1 k) (hvp k)) ▸ htie (xp k))
  have hw : w = fun k : Fin D.q => MU.pt (xq k) := funext fun k =>
    tied_unique (tq k) ((LieModel.ValAt.unique hξ (hxq1 k) (hvq k)) ▸ htie (xq k))
  subst hv hw
  have key : ∀ c₁ c₂ : V, c₁ ≠ 0 → c₂ ≠ 0 → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp (σ (.inl τ)))).restrictScalars V ≤ Submodule.span V (Set.range xp) →
      (∀ w ∈ Submodule.span V (Set.range xp), c₁ • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp (σ (.inl τ)))).restrictScalars V) →
      𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp (σ (.inr τ)))).restrictScalars V ≤ Submodule.span V (Set.range xq) →
      (∀ w ∈ Submodule.span V (Set.range xq), c₂ • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp (σ (.inr τ)))).restrictScalars V) →
      D.p * Real.log ‖jV c₁‖ ≤ Real.log ‖jL uL‖ - t ∧ Real.log ‖jL uL‖ - t ≤ -(D.q * Real.log ‖jV c₂‖) := by
    intro c₁ c₂ h1 h2 l1 u1 l2 u2
    obtain ⟨P₁, Q₁, e1, s1⟩ := exists_basis (L := L) (n := D.p) xp _ h1 l1 u1
    obtain ⟨P₂, Q₂, e2, s2⟩ := exists_basis (L := L) (n := D.q) xq _ h2 l2 u2
    obtain ⟨n1, b1, b1'⟩ := log_det_bounds jV hjV (hjV0 _ h1) e1
    obtain ⟨n2, b2, b2'⟩ := log_det_bounds jV hjV (hjV0 _ h2) e2
    have hdet : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) V), jL (P.map (algebraMap V L)).det = jV P.det := fun P =>
      (congrArg jL (RingHom.map_det (algebraMap V L) P).symm).trans (hjVe _).symm
    have m1 : (P₁.map (algebraMap V L)).det ≠ 0 := fun h => n1 (by rw [← hdet, h, map_zero])
    have m2 : (P₂.map (algebraMap V L)).det ≠ 0 := fun h => n2 (by rw [← hdet, h, map_zero])
    obtain ⟨i1, f1, k1⟩ := frame_of_matrix (n := D.p) MU Xo.univ.t.act ρC _ hMU xp hF.2.2.1 _ m1
    obtain ⟨i2, f2, k2⟩ := frame_of_matrix (n := D.q) MU Xo.univ.t.act ρC _ hMU xq hF.2.2.2 _ m2
    have r1 : (fun k : Fin D.p => ∑ i : Fin D.p, P₁ k i • xp i) =
        fun k : Fin D.p => ∑ i : Fin D.p, (P₁.map (algebraMap V L)) k i • xp i :=
      funext fun k => Finset.sum_congr rfl fun i _ => (algebraMap_smul L _ _).symm
    have r2 : (fun k : Fin D.q => ∑ i : Fin D.q, P₂ k i • xq i) =
        fun k : Fin D.q => ∑ i : Fin D.q, (P₂.map (algebraMap V L)) k i • xq i :=
      funext fun k => Finset.sum_congr rfl fun i _ => (algebraMap_smul L _ _).symm
    have I1 := hIF (σ (.inl τ)) D.p _ i1 ((congrArg (fun f => Submodule.span V (Set.range f)) r1).symm.trans s1)
    have I2 := hIF (σ (.inr τ)) D.q _ i2 ((congrArg (fun f => Submodule.span V (Set.range f)) r2).symm.trans s2)
    rw [hσp] at I1
    rw [hσq] at I2
    have hF' : IsFramed U τ.1 (ψL.comp ι) y₀ _ _ := ⟨hF.1, hF.2.1, f1, f2⟩
    have ht := hfin V L jL (ψL.comp ι) y₀ _ _ T tK mm mm' hj (by rw [← hjψ]; rfl) hF' I1 I2
    have hc := hφ.chg L (ψL.comp ι) y₀ _ _ _ _ _ _ hF hF' k1 k2
    have hne := hφ.ne L (ψL.comp ι) y₀ _ _ hF'
    have hne0 := hφ.ne L (ψL.comp ι) y₀ _ _ hF
    rw [hφu] at hc hne0
    have hc' := congrArg (fun x => Real.log ‖jL x‖) hc
    simp only [map_mul, hdet, norm_mul] at hc'
    rw [Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero jL).2 hne)) (norm_ne_zero_iff.2 n1),
      Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero jL).2 hne0)) (norm_ne_zero_iff.2 n2), ht] at hc'
    constructor <;> linarith
  refine ⟨fun hS hd => ?_, fun hS hfree κ hcp hsand d hd hd0 => ?_⟩
  · have e1 := hxp2 hS hd
    have e2 := hxq2 hS hd
    obtain ⟨k1, k2⟩ := key 1 1 one_ne_zero one_ne_zero e1.ge (fun w hw => by rw [one_smul]; exact e1.le hw) e2.ge
      (fun w hw => by rw [one_smul]; exact e2.le hw)
    rw [map_one, norm_one, Real.log_one, mul_zero] at k1 k2
    linarith
  · have hfib : InFibre 𝔐.ξ p ⟨centre z, 𝔐.all _⟩ := by
      rintro ⟨g0, g1, g2⟩
      have e1 : ((p : ℕ) : ℂ_[p]) * jV (evV ⟨_, g2⟩) = 1 := by
        rw [← map_natCast (jV.comp evV) p, RingHom.comp_apply, ← map_mul, ← map_mul, ← map_one jV, ← map_one evV]
        congr 2
        exact Subtype.ext (by simpa using mul_inv_cancel₀ g0)
      have e2 : ‖((p : ℕ) : ℂ_[p])‖ * ‖jV (evV ⟨_, g2⟩)‖ = 1 := by rw [← norm_mul, e1, norm_one]
      have a1 := norm_p_lt_one p
      have a2 := hjV (evV ⟨_, g2⟩)
      have a3 := norm_nonneg ((p : ℕ) : ℂ_[p])
      nlinarith [mul_le_mul_of_nonneg_left a2 a3]
    have hκR := (hsand _ hfib).1
    obtain ⟨z1, z2⟩ := log_norm_cp _ p (jV.comp evV) hκR hcp
    rw [RingHom.comp_apply] at z1 z2
    have hκ0 : evV ⟨κ, hκR⟩ ≠ 0 := fun h => z1 (by rw [h, map_zero])
    obtain ⟨l1, u1⟩ := hxp3 hS hfree κ _ hsand (hevV ⟨κ, hκR⟩)
    obtain ⟨l2, u2⟩ := hxq3 hS hfree κ _ hsand (hevV ⟨κ, hκR⟩)
    have hdv : jV (σ (.inl τ) d) = κ' (ι (tauIn c τ.1 d)) := by
      rw [hjVe, hκ']
      exact congrArg jL (DFunLike.congr_fun hσp d)
    have hd1 : κ' (ι (tauIn c τ.1 d)) ≠ 0 := by
      refine (map_ne_zero κ').2 ((map_ne_zero ι).2 fun h => hd0 ?_)
      have h1 : τ.1 (d : E) = 0 := congrArg Subtype.val h
      exact RingOfIntegers.coe_eq_zero_iff.1 ((map_eq_zero τ.1).1 h1)
    have hσ0 : σ (.inl τ) d ≠ 0 := fun h => hd1 (by rw [← hdv, h, map_zero])
    obtain ⟨k1, k2⟩ := key _ _ (mul_ne_zero hκ0 hσ0) (mul_ne_zero hκ0 (by rw [map_one]; exact one_ne_zero)) l1
      (u1 d fun _ => hd) l2 (u2 1 fun h => by simp at h)
    rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 z1) (norm_ne_zero_iff.2 (hdv ▸ hd1)), z2, hdv] at k1
    rw [map_one, mul_one, z2] at k2
    have a1 : 0 ≤ cP p * Real.log (p : ℕ) := by
      have := Real.log_nonpos (norm_nonneg _) (hjV (evV ⟨κ, hκR⟩))
      linarith
    have a2 : Real.log ‖κ' (ι (tauIn c τ.1 d))‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) (hdv ▸ hjV _)
    have a3 : (0 : ℝ) ≤ D.p := Nat.cast_nonneg _
    have a4 : (0 : ℝ) ≤ D.q := Nat.cast_nonneg _
    rw [abs_le]
    push_cast
    constructor <;> nlinarith [mul_nonneg a3 a1, mul_nonneg a4 a1, mul_nonneg a3 (neg_nonneg.2 a2),
      mul_nonneg a4 (neg_nonneg.2 a2)]

end RootFieldNumerics.RF
