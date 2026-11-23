import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceMain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKCT PositivityTheory.ThKF GlobalTheory.RealLift GlobalTheory.FockAlg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mem_of_weak {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (U : Submodule ℂ (SchwartzMap V ℂ)) [FiniteDimensional ℂ U]
    {x : SchwartzMap V ℂ} (h : ∀ l : SchwartzMap V ℂ →L[ℂ] ℂ, (∀ y ∈ U, l y = 0) → l x = 0) : x ∈ U := by
  by_contra hx
  obtain ⟨f, hf, hU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  let U' := U ⊔ Submodule.span ℂ {x}
  have hm : f ∘ₗ U'.subtype ∈ Submodule.span ℂ (Set.range fun y : V => (evAt y).toLinearMap ∘ₗ U'.subtype) := by
    refine FiniteDimensional.mem_span_of_iInf_ker_le_ker fun a ha => ?_
    have : a = 0 := Subtype.ext (SchwartzMap.ext fun y => (Submodule.mem_iInf _).1 ha y)
    simp [this]
  have : ∃ l : SchwartzMap V ℂ →L[ℂ] ℂ, l.toLinearMap ∘ₗ U'.subtype = f ∘ₗ U'.subtype := by
    generalize f ∘ₗ U'.subtype = g at hm
    induction hm using Submodule.span_induction with
    | mem _ hy => obtain ⟨y, rfl⟩ := hy; exact ⟨_, rfl⟩
    | zero => exact ⟨0, rfl⟩
    | add _ _ _ _ a b => obtain ⟨a, rfl⟩ := a; obtain ⟨b, rfl⟩ := b; exact ⟨a + b, rfl⟩
    | smul c _ _ a => obtain ⟨a, rfl⟩ := a; exact ⟨c • a, rfl⟩
  obtain ⟨l, hl⟩ := this
  have e : ∀ y (hy : y ∈ U'), l y = f y := fun y hy => LinearMap.congr_fun hl ⟨y, hy⟩
  refine hf ((e x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))).symm.trans (h l fun y hy => ?_))
  rw [e y (Submodule.mem_sup_left hy)]
  exact (Submodule.eq_bot_iff _).1 hU _ (Submodule.mem_map_of_mem hy)

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem actsD_of (hA : ActsLaws) (M : Model σ X W) {u} {f f₁ : SInf F (Fin n × Fin d)}
    (h : SD (fun t => M.co.rho B.ψ (realAd F t • u)) f f₁) : ActsD (evI F) (M.heisLine B.ψ u) f f₁ :=
  (hA F _ f f₁ f₁).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr]) h

theorem map_inc {lift} (hL : IsLift σ B lift) {a b : Type} (J : Matrix a b E) (w) :
    (incM F J).map (piInf (B.emb w)) = J.map (B.emb w).1 := by
  ext i j; exact hL.incl _ w

theorem gauss_fin (hA : ActsLaws) (hV : VacLine) (hF : FockEx) (hFr : FrameEx) (hB : B.IsGood σ) {lift} (hL : IsLift σ B lift)
    (M : Model σ X W) {r s r' s'} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    FiniteDimensional ℂ (Submodule.span ℂ {f | M.IsGauss B.ψ B.emb f}) := by
  choose A hA1 hA2 using fun w => hFr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC1 hC2 using fun w => hFr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hfr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, fun w => by rw [one_smul, map_inc hL]; exact hA1 w, fun w => by rw [map_inc hL]; exact hC1 w⟩
  obtain ⟨Φ, hΦ⟩ := hF F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co _ _ A C hB.cm hB.std hfr
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {Φ (PiTensorProduct.tprod ℂ fun _ => 1)})
    (Submodule.span_le.2 ?_)
  rintro f ⟨ε, hε⟩
  obtain ⟨z, hz⟩ := hV F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co _ _ A C Φ hB.cm hB.std hfr hΦ f ε fun u u' hu hu' c h1 h2 g g' p q =>
    hε u u' hu hu' (fun w => by
      have hJ : (Formalism.BasicNotions.TH.Jm r' s')ᵀ = Formalism.BasicNotions.TH.Jm r' s' := by simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]
      rw [h2, h1, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc A w * (Formalism.BasicNotions.TH.Jm r s * c w * Formalism.BasicNotions.TH.Jm r' s') * (C w)ᵀ = (A w * Formalism.BasicNotions.TH.Jm r s) * c w * (C w * Formalism.BasicNotions.TH.Jm r' s')ᵀ := by
            rw [Matrix.transpose_mul, hJ]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hA2, ← hC2, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]) g g' (actsD_of hA M p) (actsD_of hA M q)
  exact Submodule.mem_span_singleton.2 ⟨z, hz.symm⟩

section Geo

variable {ε ε' : AE F E} {x y : Fin n → AE F E} {x' y' : Fin d → AE F E} {ι : Matrix (Fin n) (Fin n₁) (AE F E)}
  {ι' : Matrix (Fin d) (Fin d₁) (AE F E)}

theorem mid_sum (w : Matrix (Fin n₁) (Fin d₁) (AE F E)) :
    ι * w * ι'ᵀ = ∑ k, ∑ l, w k l • Matrix.vecMulVec (ι *ᵥ Pi.single k 1) (ι' *ᵥ Pi.single l 1) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, Matrix.transpose_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sy_vec (M : Model σ X W) (c : AE F E) (a : Fin n → AE F E) (b : Fin d → AE F E)
    (h : (∀ z, PositivityTheory.Mix.bf (cA σ).toRingHom (incM F X.J) a (ι *ᵥ z) = 0) ∨ ∀ z, PositivityTheory.Mix.bf (cA σ).toRingHom (incM F W.J) b (ι' *ᵥ z) = 0)
    (w : Matrix (Fin n₁) (Fin d₁) (AE F E)) : sy σ X W (c • Matrix.vecMulVec a b) (ι * w * ι'ᵀ) = 0 := by
  rw [mid_sum]
  refine (form_eq M.co _ _).trans ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine (form_eq M.co _ _).symm.trans ?_
  change Algebra.trace _ _ _ = _
  rw [hTens_vec]
  rcases h with h | h <;> rw [h] <;> simp

theorem one_eq {J : Matrix (Fin n) (Fin n) (AE F E)} (o : PositivityTheory.Mix.PlaneOK (cA σ).toRingHom J ε x y ι) :
    ∃ (s t : Fin n → AE F E) (Z : Matrix (Fin n₁) (Fin n) (AE F E)), (1 : Matrix (Fin n) (Fin n) (AE F E)) = ι * Z + Matrix.vecMulVec x s + Matrix.vecMulVec y t := by
  choose s t z h using fun i => o.span (Pi.single i 1)
  refine ⟨s, t, Matrix.of fun k i => z i k, ?_⟩
  ext j i
  have := congrFun (h i) j
  simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
  rw [Matrix.one_apply, this, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.vecMulVec_apply]
  ring

theorem decompS (M : Model σ X W) (o : PositivityTheory.Mix.PlaneOK (cA σ).toRingHom (incM F X.J) ε x y ι)
    (o' : PositivityTheory.Mix.PlaneOK (cA σ).toRingHom (incM F W.J) ε' x' y' ι') {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evI F) z ∧ ∀ w : Matrix (Fin n₁) (Fin d₁) (AE F E), sy σ X W (u - ι * z * ι'ᵀ) (ι * w * ι'ᵀ) = 0 := by
  obtain ⟨s, t, Z, h⟩ := one_eq o
  obtain ⟨s', t', Z', h'⟩ := one_eq o'
  refine ⟨Z * u * Z'ᵀ, fun a ha => by rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero, Matrix.zero_mul], fun w => ?_⟩
  have e : u - ι * (Z * u * Z'ᵀ) * ι'ᵀ = (1 : AE F E) • Matrix.vecMulVec x (s ᵥ* u) + (1 : AE F E) • Matrix.vecMulVec y (t ᵥ* u) +
      (1 : AE F E) • Matrix.vecMulVec ((ι * Z * u) *ᵥ s') x' + (1 : AE F E) • Matrix.vecMulVec ((ι * Z * u) *ᵥ t') y' := by
    have e1 : u = ι * Z * u + Matrix.vecMulVec x (s ᵥ* u) + Matrix.vecMulVec y (t ᵥ* u) := by
      conv_lhs => rw [← Matrix.one_mul u, h]
      simp only [Matrix.add_mul, Matrix.vecMulVec_mul]
    have e2 : ι * Z * u = ι * (Z * u * Z'ᵀ) * ι'ᵀ + Matrix.vecMulVec ((ι * Z * u) *ᵥ s') x' + Matrix.vecMulVec ((ι * Z * u) *ᵥ t') y' := by
      conv_lhs => rw [← Matrix.mul_one (ι * Z * u), ← Matrix.transpose_one, h']
      simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.transpose_mul, Matrix.transpose_vecMulVec, Matrix.mul_vecMulVec,
        Matrix.mul_assoc]
    simp only [one_smul]
    rw [sub_eq_iff_eq_add]
    refine e1.trans ?_
    conv_lhs => rw [e2]
    abel
  rw [e]
  refine (form_eq M.co _ _).trans ?_
  rw [map_add, map_add, map_add]
  simp only [LinearMap.add_apply]
  have a1 := sy_vec (ι' := ι') M 1 x (s ᵥ* u) (Or.inl o.xi) w
  have a2 := sy_vec (ι' := ι') M 1 y (t ᵥ* u) (Or.inl o.yi) w
  have a3 := sy_vec (ι := ι) M 1 ((ι * Z * u) *ᵥ s') x' (Or.inr o'.xi) w
  have a4 := sy_vec (ι := ι) M 1 ((ι * Z * u) *ᵥ t') y' (Or.inr o'.yi) w
  rw [(form_eq M.co _ _).symm.trans a1, (form_eq M.co _ _).symm.trans a2, (form_eq M.co _ _).symm.trans a3,
    (form_eq M.co _ _).symm.trans a4]; simp

end Geo

variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
  {u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)} {ei ev}

theorem pol_fd (hA : ActsLaws) (hD : DerEx) (hV : VacLine) (hF : FockEx) (hFr : FrameEx) (hE : EvAdm) (hH : ArchHeis) (hU : ArchUniq)
    (hc : Cfg B M M₁ H H' e u) (hl : IsEvLoc M M₁ e ei ev) {lift} (hL : IsLift σ B lift)
    (V : Submodule ℂ (SInf F (Fin n × Fin d))) [FiniteDimensional ℂ V] (hP : V ≤ M.Pol B.ψ B.emb) :
    ∃ V₁ : Submodule ℂ (SInf F (Fin n₁ × Fin d₁)), FiniteDimensional ℂ V₁ ∧ V₁ ≤ M₁.Pol B.ψ B.emb ∧
      ∀ g ∈ V, ∀ c, ei (opI (M.co.rho B.ψ (lift c • u 1)) g) ∈ V₁ := by
  classical
  have hB := hc.base
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨r', s', hW⟩ := hc.skew
  obtain ⟨r₁, s₁, hX₁⟩ := hc.herm₁
  obtain ⟨r₁', s₁', hW₁⟩ := hc.skew₁
  obtain ⟨i, j, hp⟩ := hc.hH
  obtain ⟨i', j', hp'⟩ := hc.hH'
  obtain ⟨ε, oX⟩ := PositivityTheory.Mix.planeOK_herm hB hp hX
  obtain ⟨ε', oW⟩ := PositivityTheory.Mix.planeOK_skew hB hp' hW
  obtain ⟨I, hI⟩ : ∃ I, IsEv B M M₁ H.ι H'.ι I e := hc.ev.elim (fun h => ⟨_, h.1⟩) fun h => ⟨_, h.1⟩
  obtain ⟨ψ, hψ, -, hq⟩ := vac_fin hc.good
  obtain ⟨ψ₁, hψ₁, ⟨a, ha⟩, hq₁⟩ := vac_fin hc.good₁
  obtain ⟨D, hD0⟩ := hD F E σ _ _ _ B.ψ _ _ M.co hB.std
  obtain ⟨D₁, hD1⟩ := hD F E σ _ _ _ B.ψ _ _ M₁.co hB.std
  let A : Matrix (Fin n) (Fin d) (AE F E) → SInf F (Fin n × Fin d) → SInf F (Fin n₁ × Fin d₁) :=
    fun s g => ei (opI (M.co.rho B.ψ s) g)
  have hAe : ∀ s, At (evI F) s → ∀ g : SInf F (Fin n × Fin d), e (M.co.rho B.ψ s (pureA F g ψ)) = pureA F (A s g) ψ₁ :=
    fun s hs g => ev_op hH hU hB hl hψ hc.good hq hq₁ hs g
  have hval : ∀ s, At (evI F) s → ∀ (g : SInf F (Fin n × Fin d)) y, A s g y = e (M.co.rho B.ψ s (pureA F g ψ)) (ptA y a) / ψ₁ a := fun s hs g y => by
    rw [hAe s hs, pureA_ptA, mul_div_cancel_right₀ _ ha]
  have hadd : ∀ s, At (evI F) s → ∀ g g', A s (g + g') = A s g + A s g' := fun s hs g g' => SchwartzMap.ext fun y => by
    have : pureA F (g + g' : SInf F _) ψ = pureA F g ψ + pureA F g' ψ := funext fun x => add_mul _ _ _
    rw [SchwartzMap.add_apply, hval s hs, hval s hs, hval s hs, this, rho_add, map_add, Pi.add_apply, add_div]
  have hsm : ∀ s, At (evI F) s → ∀ (c : ℂ) g, A s (c • g) = c • A s g := fun s hs c g => SchwartzMap.ext fun y => by
    have : pureA F (c • g : SInf F _) ψ = c • pureA F g ψ := funext fun x => mul_assoc _ _ _
    rw [SchwartzMap.smul_apply, hval s hs, hval s hs, this, rho_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  have atR : ∀ {p q : ℕ} (t : ℝ) {v : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) v → At (evI F) (realAd F t • v) :=
    fun t v hv c hc => by rw [smul_comm, hv c hc, smul_zero]
  have hder : ∀ s, At (evI F) s → ∀ v, At (evI F) v → ∀ g : SInf F (Fin n × Fin d), ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
      HasDerivAt (fun t => l (e (M.co.rho B.ψ s (M.co.rho B.ψ (realAd F t • v) (pureA F g ψ))))) (l (pureA F (A s (D v g)) ψ₁)) 0 :=
    fun s hs v hv g l hl' => by
      obtain ⟨l', h1, h2⟩ := (hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hc.good hc.good₁).2.2 _ _ I e hI s l hl'
      have := (hD0 v hv g).1 ψ hψ l' h1
      rw [h2 _ (pureA_mem' _ hψ), hAe s hs] at this
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      exact (h2 _ (rho_mem M hB.std _ (pureA_mem' _ hψ))).symm
  let S : Set (Matrix (Fin n) (Fin d) (AE F E)) := {s | At (evI F) s ∧ ∀ w : Matrix (Fin n₁) (Fin d₁) (AE F E), sy σ X W s (incM F H.ι * w * (incM F H'.ι)ᵀ) = 0}
  have atM : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evI F) z → At (evI F) (incM F H.ι * z * (incM F H'.ι)ᵀ) :=
    fun z hz c hc => by rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz c hc, Matrix.mul_zero, Matrix.zero_mul]
  have hmid : ∀ s ∈ S, ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evI F) z → ∀ g, A s (D (incM F H.ι * z * (incM F H'.ι)ᵀ) g) = D₁ z (A s g) := fun s hs z hz g =>
    eq_of_weak fun L => by
      obtain ⟨l, hl1, hl2⟩ := exists_admissible_functional_adelic L a
      have h1 := hder s hs.1 _ (atM z hz) g l hl1
      have h2 := (hD1 z hz (A s g)).1 ψ₁ hψ₁ l hl1
      have : (fun t => l (e (M.co.rho B.ψ s (M.co.rho B.ψ (realAd F t • (incM F H.ι * z * (incM F H'.ι)ᵀ)) (pureA F g ψ))))) =
          fun t => l (M₁.co.rho B.ψ (realAd F t • z) (pureA F (A s g) ψ₁)) := funext fun t => by
        have h0 := hs.2 (realAd F t • z)
        unfold sy at h0
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, rho_comm, h0, AddChar.map_zero_eq_one, one_smul,
          hI.Heisenberg₂ _ _ (rho_mem M hB.std _ (pureA_mem' _ hψ)), hAe s hs.1]
      rw [this] at h1
      have h3 := h1.unique h2
      rw [hl2 _ _ hψ₁, hl2 _ _ hψ₁] at h3
      exact mul_left_cancel₀ ha h3
  have hort : ∀ (V₁ : Submodule ℂ (SInf F (Fin n₁ × Fin d₁))) [FiniteDimensional ℂ V₁] g, (∀ s ∈ S, A s g ∈ V₁) →
      ∀ v ∈ S, ∀ s ∈ S, A s (D v g) ∈ V₁ := fun V₁ _ g hg v hv s hs => mem_of_weak V₁ fun L hL0 => by
    obtain ⟨l, hl1, hl2⟩ := exists_admissible_functional_adelic L a
    have h1 := hder s hs.1 v hv.1 g l hl1
    have : (fun t => l (e (M.co.rho B.ψ s (M.co.rho B.ψ (realAd F t • v) (pureA F g ψ))))) = fun _ => 0 := funext fun t => by
      have hS : s + realAd F t • v ∈ S := ⟨fun c hc => by rw [smul_add, hs.1 c hc, atR t hv.1 c hc, add_zero], fun w => by
        have p1 := (form_eq M.co _ _).symm.trans (hs.2 w)
        have p2 := (form_eq M.co _ _).symm.trans (hv.2 w)
        refine (form_eq M.co _ _).trans ?_
        rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, p1, p2, smul_zero, add_zero]⟩
      rw [rho_rho, map_smul, map_smul, hAe _ hS.1, hl2 _ _ hψ₁, hL0 _ (hg _ hS), mul_zero, smul_zero]
    rw [this] at h1
    have h3 := h1.unique (hasDerivAt_const _ _)
    rw [hl2 _ _ hψ₁] at h3
    exact (mul_eq_zero.1 h3).resolve_left ha
  have uq : ∀ v, At (evI F) v → ∀ g g₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ v) g g₁ → g₁ = D v g :=
    fun v hv g g₁ h => (hA F _ g g₁ _).2.2.1 _ h (actsD_of hA M (hD0 v hv g).1)
  have uq₁ : ∀ v, At (evI F) v → ∀ g g₁ : SInf F (Fin n₁ × Fin d₁), ActsD (evI F) (M₁.heisLine B.ψ v) g g₁ → g₁ = D₁ v g :=
    fun v hv g g₁ h => (hA F _ g g₁ _).2.2.1 _ h (actsD_of hA M₁ (hD1 v hv g).1)
  have polD : ∀ z, At (evI F) z → ∀ g ∈ M₁.Pol B.ψ B.emb, D₁ z g ∈ M₁.Pol B.ψ B.emb := fun z hz g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 z hz g (Submodule.mem_sInf.1 hg N hN) _ (actsD_of hA M₁ (hD1 z hz g).1)
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {g | ∃ V₁ : Submodule ℂ (SInf F (Fin n₁ × Fin d₁)), FiniteDimensional ℂ V₁ ∧ V₁ ≤ M₁.Pol B.ψ B.emb ∧ ∀ s ∈ S, A s g ∈ V₁}
      add_mem' := by
        rintro g g' ⟨V₁, f1, p1, h1⟩ ⟨V₂, f2, p2, h2⟩
        exact ⟨V₁ ⊔ V₂, inferInstance, sup_le p1 p2, fun s hs => by
          rw [hadd s hs.1]; exact Submodule.add_mem_sup (h1 s hs) (h2 s hs)⟩
      zero_mem' := ⟨⊥, inferInstance, bot_le, fun s hs => by
        have := hsm s hs.1 0 0
        rw [zero_smul, zero_smul] at this
        rw [this]; exact zero_mem _⟩
      smul_mem' := by
        rintro c g ⟨V₁, f1, p1, h1⟩
        exact ⟨V₁, f1, p1, fun s hs => by rw [hsm s hs.1]; exact V₁.smul_mem c (h1 s hs)⟩ }
  have hN : M.Pol B.ψ B.emb ≤ N := by
    refine sInf_le ⟨fun g hg => ?_, fun v hv g hg g₁ hg₁ => ?_⟩
    · refine ⟨_, gauss_fin hA hV hF hFr hB hL M₁ hX₁ hW₁, Submodule.span_le.2 fun f hf => Submodule.mem_sInf.2 fun N hN => hN.1 f hf,
        fun s hs => Submodule.subset_span ?_⟩
      obtain ⟨η, hη⟩ := hg
      refine ⟨η, fun z z' hz hz' hzz f f' hf hf' => ?_⟩
      rw [uq₁ z hz _ _ hf, uq₁ z' hz' _ _ hf', ← hmid s hs z hz, ← hmid s hs z' hz', ← hsm s hs.1]
      congr 1
      refine hη _ _ (atM z hz) (atM z' hz') (fun w => ?_) _ _ (actsD_of hA M (hD0 _ (atM z hz) g).1) (actsD_of hA M (hD0 _ (atM z' hz') g).1)
      simp only [Matrix.map_mul, Matrix.transpose_map, map_inc hL, hzz, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc _ = (H.ι.map (B.emb w).1 * X₁.θ w) * z.map (piInf (B.emb w)) * (H'.ι.map (B.emb w).1 * W₁.θ w)ᵀ := by
            rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [← (hp.cartan w).1, ← (hp'.cartan w).1, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    · obtain ⟨V₁, f1, p1, h1⟩ := hg
      obtain ⟨z, hz, hzo⟩ := decompS M oX oW hv
      have hv0 : v - incM F H.ι * z * (incM F H'.ι)ᵀ ∈ S :=
        ⟨fun c hc => by rw [smul_sub, hv c hc, atM z hz c hc, sub_zero], hzo⟩
      have hs : D v g = D (incM F H.ι * z * (incM F H'.ι)ᵀ) g + D (v - incM F H.ι * z * (incM F H'.ι)ᵀ) g := by
        ext x
        rw [SchwartzMap.add_apply, (hD0 v hv g).2, (hD0 _ (atM z hz) g).2, (hD0 _ hv0.1 g).2]
        have e1 : (fun i => evI F ((M.co.e (v - incM F H.ι * z * (incM F H'.ι)ᵀ)).1 i)) =
            (fun i => evI F ((M.co.e v).1 i)) - fun i => evI F ((M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1 i) := by
          funext i; rw [map_sub]; exact map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
        have e2 : ∀ i, evI F ((M.co.e (v - incM F H.ι * z * (incM F H'.ι)ᵀ)).2 i) =
            evI F ((M.co.e v).2 i) - evI F ((M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2 i) := fun i => by
          rw [map_sub]; exact map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
        rw [e1]
        simp only [e2, map_sub (fderiv ℝ g x), map_sub (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), mul_sub,
          Finset.sum_sub_distrib, Complex.ofReal_sub]
        ring
      refine ⟨V₁.map (D₁ z).toLinearMap ⊔ V₁, inferInstance, sup_le ?_ p1, fun s hs' => ?_⟩
      · rintro _ ⟨y, hy, rfl⟩; exact polD z hz y (p1 hy)
      · rw [uq v hv _ _ hg₁, hs, hadd s hs'.1, hmid s hs' z hz]
        exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (h1 s hs')) (hort V₁ g h1 _ hv0 s hs')
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  choose V₁ f1 p1 h1 using fun g : t => hN (hP (ht ▸ Submodule.subset_span g.2))
  refine ⟨⨆ g, V₁ g, inferInstance, iSup_le p1, fun g hg c => ?_⟩
  have hS : lift c • u 1 ∈ S := ⟨at_smul (hL.supp c) _, fun w => by
    rcases hc.ev with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · simpa only [shiftA, Units.val_one, one_smul] using sy_vec M (lift c) _ _ (Or.inl oX.xi) w
    · simpa only [shiftB, Units.val_one, map_one, one_smul] using sy_vec M (lift c) _ _ (Or.inl oX.yi) w⟩
  change A _ g ∈ _
  rw [← ht] at hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact Submodule.mem_iSup_of_mem ⟨x, hx⟩ (h1 ⟨x, hx⟩ _ hS)
  | zero =>
    have := hsm _ hS.1 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]; exact zero_mem _
  | add _ _ _ _ p q => rw [hadd _ hS.1]; exact add_mem p q
  | smul c _ _ p => rw [hsm _ hS.1]; exact Submodule.smul_mem _ c p

theorem archCone_of (hDi : ArchDict) (hSt : StabEx) (hO : ArchOp) (hS : Slice) (hH : ArchHeis) (hU : ArchUniq) (hI : SchInt)
    (hA : ActsLaws) (hD : DerEx) (hV : VacLine) (hF : FockEx) (hFr : FrameEx) (hE : EvAdm) (hK' : KFinData) : ArchCone := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hc hl K m hK hm χX χW om r s r' s' hP ν z hν hz
  obtain ⟨lift, hL⟩ := hDi F E σ B hc.base
  obtain ⟨L, h⟩ := cone_core hSt hO hS hH hU hI hc hl hL hK hm hP ν z hν hz
  refine ⟨L, fun f y => ?_, fun f hf => ?_, fun f y => ⟨(h f (evAt y)).1, (h f (evAt y)).2.1⟩⟩
  · rw [← evAt_apply y (L f), (h f (evAt y)).2.2]
    simp only [evAt_apply, wt, mul_assoc]
  · obtain ⟨T, hT, hTp, -, -⟩ := k_ops hSt hO hK hP
    obtain ⟨cc, -, -, hce⟩ := shift_eq hc hL
    obtain ⟨ψ, hψ, ⟨a, ha⟩, hq⟩ := vac_fin hP.good
    have hfin := (hK' F E σ B n d X W M χX χW om r s r' s' hP K hK (pure f M.vac) (Submodule.subset_span
      ⟨f, hf, M.vac, fun v => (hP.good.vac v).1, Eventually.of_forall fun _ => rfl, rfl⟩)).2
    let j : SInf F (Fin n × Fin d) →ₗ[ℂ] Fn F n d :=
      { toFun := fun g => pureA F g ψ
        map_add' := fun g g' => funext fun x => add_mul _ _ _
        map_smul' := fun c g => funext fun x => mul_assoc _ _ _ }
    have hj : Function.Injective j := fun g g' hg => SchwartzMap.ext fun y => by
      have := congrFun hg (ptA y a)
      change pureA F g ψ _ = pureA F g' ψ _ at this
      rw [pureA_ptA, pureA_ptA] at this
      exact mul_right_cancel₀ ha this
    let V := Submodule.span ℂ (Set.range fun k => T k f)
    haveI : FiniteDimensional ℂ V := by
      unfold KFinite at hfin
      refine FiniteDimensional.of_injective (j.restrict (p := V) (q := Submodule.span ℂ (Set.range fun k : K => om (k.1, 1) (pure f M.vac)))
        fun g hg => ?_) fun a b hab => Subtype.ext (hj (congrArg Subtype.val hab))
      refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap j _)).2 ?_ hg)
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨⟨k.1, (mem_kAt.1 k.2).1⟩, ?_⟩
      change om (k.1, 1) (pure f M.vac) = pureA F (T k f) ψ
      rw [hq]; exact (hT k).1 f ψ hψ
    obtain ⟨V₁, f1, p1, h1⟩ := pol_fd hA hD hV hF hFr hE hH hU hc hl hL V (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hTp k f hf))
    refine p1 (mem_of_weak V₁ fun l hl0 => ?_)
    rw [(h f l).2.2]
    have : ∀ (k : kAt K (evI F)) (t : idAt E (evI F)),
        l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) = 0 := fun k t => by
      rw [hce, op_comp hH hU hP (hT k) (at_smul (hL.supp _) _)]
      exact hl0 _ (h1 _ (Submodule.subset_span ⟨k, rfl⟩) _)
    simp [this]

end PositivityTheory.ThKG.Loc.Bump

end
