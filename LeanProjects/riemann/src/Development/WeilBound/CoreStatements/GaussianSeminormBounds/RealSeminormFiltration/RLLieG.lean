import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieE
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieF

noncomputable section

open scoped TensorProduct Matrix Classical RealInnerProductSpace Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealWeil Complex

namespace PositivityTheory.RL.Up

section Inv

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [Fintype β]

theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hTens_actB [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB) (x y : Matrix α β E) :
    hTens c JA JB (actB c g x) (actB c g y) = hTens c JA JB x y := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
  rw [hTens_eq, hTens_eq]
  have : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    unfold actB
    rw [show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E)ᵀ).map c from
      Matrix.map_mul (f := c.toRingHom), Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    conv_rhs => rw [← hg]
    simp only [Matrix.mul_assoc]
  rw [this]

end Inv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ext_at (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m n : Type} {X X' : Matrix m n (AE F E)}
    (hx : At (evI F) (X - X')) (hinf : ∀ w, X.map (piInf (τ w)) = X'.map (piInf (τ w))) : X = X' := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf h τ _ (fun u hu => congrFun (congrFun (hx u hu) i) j) fun w => ?_)
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun (hinf w) i) j

theorem At.sub' {M : Type} [AddCommGroup M] [Module (AF F) M] {a b : M} (ha : At (evI F) a) (hb : At (evI F) b) :
    At (evI F) (a - b) := fun u hu => by rw [smul_sub, ha u hu, hb u hu, sub_zero]

theorem exists_lf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (m n : Type) :
    ∃ L : (InfinitePlace F → Matrix m n ℂ) → Matrix m n (AE F E), Continuous L ∧ (∀ z, At (evI F) (L z)) ∧
      ∀ z w, (L z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hs'⟩ := exists_section h τ
  refine ⟨fun z => Matrix.of fun i j => s fun w => z w i j,
    continuous_matrix fun i j => hs.comp (continuous_pi fun w => (continuous_apply w).matrix_elem i j),
    fun z a ha => ?_, fun z w => ?_⟩
  · ext i j
    exact (hs' _).1 a ha
  · ext i j
    exact (hs' _).2 w

variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem exists_iota (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E))
    (K : InfinitePlace F → Matrix β β ℂ)
    (hK : ∀ w (g : Matrix β β ℂ), gᴴ * K w * g = K w → gᵀ * J.map (piInf (τ w)) * g.map star = J.map (piInf (τ w))) :
    ∃ ι : SG K →* UG (cA σ) J, Continuous ι ∧ (∀ g, At (evI F) (((ι g).1 : Matrix β β (AE F E)) - 1)) ∧
      ∀ g w, ((ι g).1 : Matrix β β (AE F E)).map (piInf (τ w)) = g.1.1 w := by
  obtain ⟨L, hc, hL, hL'⟩ := exists_lf h τ β β
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hG : ∀ (a : InfinitePlace F → Matrix β β ℂ) w, (1 + L (a - 1)).map (piInf (τ w)) = a w := fun a w => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hL']
    simp
  let G : (InfinitePlace F → Matrix β β ℂ) →* Matrix β β (AE F E) :=
    { toFun := fun a => 1 + L (a - 1)
      map_one' := ext_at h τ (fun u hu => by rw [add_sub_cancel_left, hL _ u hu]) fun w => by
        rw [hG, Matrix.map_one _ (map_zero _) (map_one _)]
        rfl
      map_mul' := fun a c => ext_at h τ (fun u hu => by
        have e : (1 + L (a * c - 1)) - (1 + L (a - 1)) * (1 + L (c - 1)) =
            L (a * c - 1) - L (c - 1) - L (a - 1) * (1 + L (c - 1)) := by noncomm_ring
        rw [e, smul_sub, smul_sub, ← Matrix.smul_mul, hL _ u hu, hL _ u hu, hL _ u hu]
        simp) fun w => by
        rw [Matrix.map_mul, hG, hG, hG]
        rfl }
  have hGc : Continuous G := continuous_const.add (hc.comp (continuous_id.sub continuous_const))
  have hGU : ∀ g : SG K, (G g.1.1)ᵀ * J * (G g.1.1).map (cA σ) = J := fun g => by
    refine ext_at h τ (fun u hu => ?_) fun w => ?_
    · set N := L (g.1.1 - 1)
      have hN : u • N = 0 := hL _ u hu
      have e0 : (G g.1.1).map (cA σ) = 1 + N.map (cA σ) := by
        show (1 + N).map _ = _
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      have e : (G g.1.1)ᵀ * J * (G g.1.1).map (cA σ) - J = Nᵀ * (J * (G g.1.1).map (cA σ)) + J * N.map (cA σ) := by
        rw [e0]
        show (1 + N)ᵀ * _ * _ - _ = _
        simp only [Matrix.transpose_add, Matrix.transpose_one]
        noncomm_ring
      have e1 : u • N.map (cA σ) = 0 := by
        ext i j
        have := congrArg (cA σ) (congrFun (congrFun hN i) j)
        simpa using this
      rw [e, smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, e1, ← Matrix.transpose_smul, hN]
      simp
    · rw [map_form h, show (G g.1.1).map (piInf (τ w)) = _ from hG _ w]
      exact hK w _ (congrFun (show star g.1.1 * K * g.1.1 = K from g.2) w)
  refine ⟨((Units.map G).comp (SG K).subtype).codRestrict _ hGU,
    ((Continuous.units_map G hGc).comp continuous_subtype_val).subtype_mk _, fun g u hu => ?_, fun g w => hG _ w⟩
  show u • (1 + L (g.1.1 - 1) - 1) = 0
  rw [add_sub_cancel_left, hL _ u hu]

variable (σ) in

def sB (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (u v : Matrix α β (AE F E)) : ℝ :=
  -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u v))

def IsD {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)) : Prop :=
  ∀ u, At (evI F) u → ∀ f x, D u f x = fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x

variable {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}

theorem at_e {u : Matrix α β (AE F E)} (hu : At (evI F) u) : At (evI F) (d.e u) := fun s hs => by
  rw [← map_smul, hu s hs, map_zero]

theorem at_symm {p} (hp : At (evI F) p) : At (evI F) (d.e.symm p) := fun s hs => by
  rw [← map_smul, hp s hs, map_zero]

theorem sympl_e {l : Type} [Fintype l] (c : Co F κ l) (u v : Matrix α β (AE F E)) :
    sympl (c.vec (d.e u)) (c.vec (d.e v)) = sB σ JA JB u v := by
  rw [c.sympl_vec, sB, d.form]

theorem IsD.P {D} (hD : IsD d D) {l : Type} [Fintype l] (c : Co F κ l) {u : Matrix α β (AE F E)} (hu : At (evI F) u)
    (f : Sch l) : c.P (dRho (c.vec (d.e u)) f) = D u (c.P f) := by
  ext x
  rw [c.P_dRho, hD u hu]

theorem IsD.comm {D} (hD : IsD d D) {u v : Matrix α β (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v) (f : SInf F κ) :
    D u (D v f) = D v (D u f) + (2 * π * I * sB σ JA JB u v) • f := by
  obtain ⟨n, ⟨c⟩⟩ := exists_co F κ
  have := congrArg (fun L => c.P (L (c.P' f))) (dRho_comm (c.vec (d.e u)) (c.vec (d.e v)))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, map_sub, map_smul, hD.P c hu, hD.P c hv, c.P_P', sympl_e] at this
  rw [← this]
  abel

theorem main (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (h : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (K : InfinitePlace F → Matrix β β ℂ) (hK : ∀ w, (K w)ᴴ = K w)
    (hu : ∀ w, IsUnit (K w).det)
    (hKJ : ∀ w (g : Matrix β β ℂ), gᴴ * K w * g = K w ↔ gᵀ * JB.map (piInf (τ w)) * g.map star = JB.map (piInf (τ w)))
    {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)} (hom : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    {D} (hD : IsD d D) :
    ∃ c : InfinitePlace F → ℂ, ∀ γ ∈ RLines σ JB, ∀ Z : InfinitePlace F → Matrix β β ℂ,
      (∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = NormedSpace.exp (t • Z w)) →
      ∀ (ι : Type) [Fintype ι] (u v : ι → Matrix α β (AE F E)), (∀ j, At (evI F) (u j)) → (∀ j, At (evI F) (v j)) →
        (∀ x, At (evI F) x → ∀ w, x.map (piInf (τ w)) * (Z w)ᵀ = ∑ j, sB σ JA JB (v j) x • (u j).map (piInf (τ w))) →
        ∀ f, SD (fun t => om (γ (Multiplicative.ofAdd t))) f
          ((8 * π * I : ℂ)⁻¹ • ∑ j, (D (u j) (D (v j) f) + D (v j) (D (u j) f)) + (∑ w, c w * (Z w).trace) • f) := by
  obtain ⟨n, ⟨c⟩⟩ := exists_co F κ
  obtain ⟨M⟩ := exists_meta (l := Fin n) hP
  obtain ⟨ι, hιc, hι, hι'⟩ := exists_iota h τ JB K fun w g => (hKJ w g).1
  obtain ⟨L, -, hL, hL'⟩ := exists_lf h τ α β
  have hLu : ∀ u, At (evI F) u → L (fun w => u.map (piInf (τ w))) = u := fun u hu =>
    ext_at h τ (At.sub' (hL _) hu) (hL' _)
  let E0 : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    { toFun := fun z => c.vec (d.e (L z))
      map_add' := fun z z' => by
        rw [← c.vec_add, ← map_add]
        congr 2
        refine ext_at h τ (At.sub' (hL _) fun a ha => by rw [smul_add, hL _ a ha, hL _ a ha, add_zero]) fun w => ?_
        rw [Matrix.map_add _ (map_add _), hL', hL', hL']
        rfl
      map_smul' := fun t z => by
        rw [RingHom.id_apply, ← c.vec_smul, ← map_smul]
        congr 2
        refine ext_at h τ (At.sub' (hL _) fun a ha => by rw [smul_comm, hL _ a ha, smul_zero]) fun w => ?_
        rw [hL']
        ext i j
        refine Eq.trans ?_ (Fock.piInf_realAd h.1 (τ w) t _).symm
        rw [show piInf (τ w) (L z i j) = z w i j from congrFun (congrFun (hL' z w) i) j]
        rfl }
  have hE0 : ∀ u, At (evI F) u → E0 (fun w => u.map (piInf (τ w))) = c.vec (d.e u) := fun u hu =>
    congrArg (fun x => c.vec (d.e x)) (hLu u hu)
  have hsurj : ∀ w, ∃ u, At (evI F) u ∧ c.vec (d.e u) = w := fun w => by
    obtain ⟨p, hp, rfl⟩ := c.exists_vec w
    exact ⟨d.e.symm p, at_symm hp, by rw [LinearEquiv.apply_symm_apply]⟩
  let Ee := LinearEquiv.ofBijective E0 ⟨(injective_iff_map_eq_zero _).2 fun z hz => by
    have h1 : L z = 0 := d.e.map_eq_zero_iff.1 (c.eq_zero_of_vec (at_e (hL z)) hz)
    funext w
    rw [← hL' z, h1, Matrix.map_zero _ (map_zero _)]
    rfl, fun w => by
    obtain ⟨u, hu, rfl⟩ := hsurj w
    exact ⟨_, hE0 u hu⟩⟩
  let Rm : (InfinitePlace F → Matrix β β ℂ) →ₐ[ℝ] Module.End ℝ (InfinitePlace F → Matrix α β ℂ) :=
    AlgHom.ofLinearMap (LinearMap.mk₂ ℝ (fun a z w => z w * (a w)ᵀ)
      (fun _ _ _ => by funext w; simp [Matrix.mul_add]) (fun _ _ _ => by funext w; simp)
      (fun _ _ _ => by funext w; simp [Matrix.add_mul]) (fun _ _ _ => by funext w; simp))
      (LinearMap.ext fun z => by funext w; simp)
      (fun a b => LinearMap.ext fun z => by funext w; simp [Matrix.mul_assoc])
  let ρ : (InfinitePlace F → Matrix β β ℂ) →ₐ[ℝ] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv' : _ ≃ₐ[ℝ] _).toAlgHom.comp ((Ee.conjAlgEquiv ℝ).toAlgHom.comp Rm)
  have hρ : ∀ a z, ρ a *ᵥ E0 z = E0 fun w => z w * (a w)ᵀ := fun a z => by
    have : ρ a *ᵥ Ee z = Ee (Rm a (Ee.symm (Ee z))) :=
      LinearMap.toMatrix'_mulVec (Ee.conjAlgEquiv ℝ (Rm a)) (Ee z)
    rw [Ee.symm_apply_apply] at this
    exact this
  have hat : ∀ (g : UG (cA σ) JB) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (actB (cA σ) g u) := fun g u hu a ha => by
    rw [actB, ← Matrix.smul_mul, hu a ha, Matrix.zero_mul]
  have hact : ∀ (g : SG K) (u : Matrix α β (AE F E)), At (evI F) u → ρ g.1.1 *ᵥ c.vec (d.e u) = c.vec (d.e (actB (cA σ) (ι g) u)) :=
    fun g u hu => by
      rw [← hE0 u hu, ← hE0 _ (hat _ u hu), hρ]
      congr 1
      funext w
      rw [actB, Matrix.map_mul, Matrix.transpose_map, hι']
  have hsp : ∀ g : SG K, ρ g.1.1 ∈ Matrix.symplecticGroup (Fin n) ℝ := fun g => mem_sp_of _ fun w w' => by
    obtain ⟨u, hu, rfl⟩ := hsurj w
    obtain ⟨u', hu', rfl⟩ := hsurj w'
    rw [hact g u hu, hact g u' hu', sympl_e, sympl_e, sB, sB, symp, symp, hTens_actB]
  have step : ∀ (g : SG K) g', (M.pr g' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = ρ g.1.1 → ∃ z : ℂ,
      ∀ f, ∀ gf ∈ SB (κ → Af F), om (ι g) (pureA F (c.P f) gf) = pureA F (c.P ((z • M.om g') f)) gf := fun g g' hg => by
    obtain ⟨z, hz⟩ := c.schur2 hψ (om (ι g)) (hom.adm _) (M.om g'⁻¹) (fun w hw Φ hΦ => by
      have := hom.impl (ι g) (d.e.symm w) Φ hΦ
      have e : actB (cA σ) (ι g) (d.e.symm w) = d.e.symm w := by
        have e1 : pairA F 0 1 • d.e.symm w = d.e.symm w := by rw [← map_smul, hw]
        have e2 := hι g (pairA F 0 1) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
        rw [actB, ← sub_eq_zero]
        conv_lhs => rw [← Matrix.mul_one (d.e.symm w), Matrix.mul_assoc, Matrix.one_mul, ← Matrix.mul_sub, ← e1,
          Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_one, ← Matrix.transpose_sub, ← Matrix.transpose_smul, e2]
        simp
      rw [e, Darboux.rho, LinearEquiv.apply_symm_apply] at this
      exact this) fun w hw f gf hgf => by
      have h1 : (M.pr g'⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = ρ (g⁻¹).1.1 := by
        have a : (M.pr g' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) * ρ (g⁻¹).1.1 = 1 := by
          rw [hg, ← map_mul]
          exact (congrArg ρ (Units.mul_inv g.1)).trans (map_one ρ)
        have b : (M.pr g'⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) * M.pr g' = 1 := by
          rw [← Submonoid.coe_mul, ← map_mul, inv_mul_cancel, map_one, Submonoid.coe_one]
        exact left_inv_eq_right_inv b a
      have hu := at_symm (d := d) hw
      have h2 := hact g⁻¹ _ hu
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [M.cov, h1, h2, ← c.schr_P hψ (at_e (hat _ _ hu))]
      have := hom.impl (ι g) (actB (cA σ) (ι g⁻¹) (d.e.symm w)) _ (pure_mem (c.P (M.om g'⁻¹ f)) hgf)
      rw [show actB (cA σ) (ι g) (actB (cA σ) (ι g⁻¹) (d.e.symm w)) = d.e.symm w by
        rw [actB, actB, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, ← map_mul,
          mul_inv_cancel, map_one]
        simp] at this
      conv_rhs at this => rw [Darboux.rho, LinearEquiv.apply_symm_apply]
      exact this
    refine ⟨z, fun f gf hgf => ?_⟩
    have := hz (M.om g' f) gf hgf
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply] at this
    rw [this, ContinuousLinearMap.smul_apply, map_smul]
    funext x
    simp [pureA, mul_assoc]
  have ex : ∀ g : SG K, ∃ A : Sch (Fin n) →L[ℂ] Sch (Fin n),
      ∀ f, ∀ gf ∈ SB (κ → Af F), om (ι g) (pureA F (c.P f) gf) = pureA F (c.P (A f)) gf := fun g => by
    obtain ⟨g', hg'⟩ := M.quot.surjective ⟨_, hsp g⟩
    obtain ⟨z, hz⟩ := step g g' (congrArg Subtype.val hg')
    exact ⟨_, hz⟩
  choose A0 hA0 using ex
  have uniq : ∀ (g : SG K) (B : Sch (Fin n) →L[ℂ] Sch (Fin n)),
      (∀ f, ∀ gf ∈ SB (κ → Af F), om (ι g) (pureA F (c.P f) gf) = pureA F (c.P (B f)) gf) → A0 g = B := fun g B hB => by
    ext1 f
    rw [← c.P'_P (A0 g f), ← c.P'_P (B f)]
    congr 1
    exact SeminormBoundRestriction.eq_of_pureA fun gf hgf x => by rw [← hA0 g f gf hgf, hB f gf hgf]
  let A : SG K →* (Sch (Fin n) →L[ℂ] Sch (Fin n)) :=
    { toFun := A0
      map_one' := uniq _ _ fun f gf _ => by rw [map_one, map_one]; rfl
      map_mul' := fun a b => uniq _ _ fun f gf hgf => by
        rw [map_mul, map_mul, Module.End.mul_apply, hA0 b f gf hgf, hA0 a _ gf hgf]
        rfl }
  obtain ⟨cc, hcc⟩ := mid M K hK hu ρ hsp A (fun g g' hg => (step g g' hg).imp fun z hz => uniq _ _ hz) fun T f => by
    obtain ⟨l, hl, gf, hgf, hT⟩ := exists_adm (T ∘L c.P')
    refine ((hom.cont l hl _ (pure_mem (c.P f) hgf)).comp hιc).congr fun g => ?_
    show l _ = T (A0 g f)
    rw [hA0 g f gf hgf, hT, ContinuousLinearMap.comp_apply, c.P'_P]
  refine ⟨cc, fun γ hγ Z hZ J _ u v hu hv huv f gf hgf l hl => ?_⟩
  obtain ⟨T, hT⟩ := hl gf hgf
  let mp : Matrix β β (AE F E) →* (InfinitePlace F → Matrix β β ℂ) :=
    MonoidHom.pi fun w => (piInf (τ w)).mapMatrix.toMonoidHom
  let γ0 : ℝ → SG K := fun t => ⟨Units.map mp (γ (Multiplicative.ofAdd t)).1, funext fun w => (hKJ w _).2 (by
    have := congrArg (fun X : Matrix β β (AE F E) => X.map (piInf (τ w))) (γ (Multiplicative.ofAdd t)).2
    simp only [map_form h] at this
    exact this)⟩
  have e0 : ∀ t, γ (Multiplicative.ofAdd t) = ι (γ0 t) := fun t => Subtype.ext (Units.ext (ext_at h τ (by
    have := At.sub' (hγ.2 (Multiplicative.ofAdd t)) (hι (γ0 t))
    rwa [sub_sub_sub_cancel_right] at this) fun w => (hι' (γ0 t) w).symm))
  have hq := quad_eq (ρ Z) (fun j => c.vec (d.e (u j))) (fun j => c.vec (d.e (v j))) fun w => by
    obtain ⟨x, hx, rfl⟩ := hsurj w
    simp only [sympl_e]
    rw [← hE0 x hx, hρ]
    simp only [huv x hx, ← hE0 _ (hu _), ← map_smul, ← map_sum]
    congr 1
    funext w
    simp [Finset.sum_apply]
  have := hcc Z γ0 hZ (T ∘L c.P) (c.P' f)
  rw [hT]
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => ?_)
  · rw [ContinuousLinearMap.comp_apply, hq]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply, map_add, map_smul, map_sum, hD.P c (hu _), hD.P c (hv _), c.P_P']
  · show l _ = T (c.P (A0 (γ0 t) (c.P' f)))
    rw [← hT, ← hA0 _ _ gf hgf, c.P_P', ← e0]

end PositivityTheory.RL.Up

end
