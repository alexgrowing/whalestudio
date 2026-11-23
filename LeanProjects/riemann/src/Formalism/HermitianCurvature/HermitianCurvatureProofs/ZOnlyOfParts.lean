import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffOnInvConjDet

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

section transfer

variable {k r j : ℕ} (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))

def Good (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : Prop :=
  (p.val < j ∧ q.val < j) ∨ (2 * r + k < p.val + j ∧ 2 * r + k < q.val + j)

theorem rdV_levi (hC : CurveLevi) (x : MJ j) (f : Q.Mx k r → E) (Z : MJ j) :
    RdV (levi k r j x) f (x0 k r j hj Z τ γ) = RdV x (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold RdV
  congr 1
  funext t
  rw [hC k r j hj Z τ γ x t]

theorem EopZ_e (a b : Fin j) :
    EopZ (E := E) k r j (eI k r (Fin.castLE (by omega) a)) (eI k r (Fin.castLE (by omega) b)) = EZ a b := by
  unfold EopZ
  simp [eI]

theorem EopZ_es (a b : Fin j) :
    EopZ (E := E) k r j (esI k r (Fin.castLE (by omega) a)) (esI k r (Fin.castLE (by omega) b)) = EZs a b := by
  unfold EopZ
  have ha := a.isLt
  have hb := b.isLt
  rw [dif_neg (by simp [esI]; omega), dif_pos (by simp [esI]; omega), dif_pos (by simp [esI]; omega)]
  congr 1 <;> ext <;> simp [esI] <;> omega

theorem eab_pull (hC : CurveLevi) (hH : HpartLevi) (p q : Fin (2 * r + k + 1)) (hpq : Good k r j p q)
    (f : Q.Mx k r → E) (Z : MJ j) :
    EabH (Hpk k r) p q f (x0 k r j hj Z τ γ) = EopZ k r j p q (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  have hjr : j ≤ r := by omega
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Fin j, p = eI k r (Fin.castLE hjr a) := ⟨⟨p.val, hp⟩, Fin.ext rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin j, q = eI k r (Fin.castLE hjr b) := ⟨⟨q.val, hq⟩, Fin.ext rfl⟩
    rw [EopZ_e hj]
    unfold EabH EZ
    rw [(hH k r j hjr a b).1, (hH k r j hjr a b).2.1, rdV_levi hj τ γ hC, rdV_levi hj τ γ hC]
  · have hp2 := p.isLt
    have hq2 := q.isLt
    obtain ⟨a, rfl⟩ : ∃ a : Fin j, p = esI k r (Fin.castLE hjr a) :=
      ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin j, q = esI k r (Fin.castLE hjr b) :=
      ⟨⟨2 * r + k - q.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩
    rw [EopZ_es hj]
    unfold EabH EZs
    rw [(hH k r j hjr a b).2.2.1, (hH k r j hjr a b).2.2.2, rdV_levi hj τ γ hC, rdV_levi hj τ γ hC]

theorem top_pull (hC : CurveLevi) (hH : HpartLevi) (u : ℂ) (p q : Fin (2 * r + k + 1)) (hpq : Good k r j p q)
    (f : Q.Mx k r → E) (Z : MJ j) :
    QuantumDeterminants.Top (EabH (Hpk k r)) u p q f (x0 k r j hj Z τ γ) =
      TopG (EopZ k r j) u p q (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold QuantumDeterminants.Top TopG
  rw [eab_pull hj τ γ hC hH p q hpq]

def Rel (T : (Q.Mx k r → E) → Q.Mx k r → E) (S : (MJ j → E) → MJ j → E) : Prop :=
  ∀ (f : Q.Mx k r → E) (Z : MJ j), T f (x0 k r j hj Z τ γ) = S (fun Z' => f (x0 k r j hj Z' τ γ)) Z

theorem foldr_pull : ∀ (L₁ : List ((Q.Mx k r → E) → Q.Mx k r → E)) (L₂ : List ((MJ j → E) → MJ j → E)),
    List.Forall₂ (Rel (E := E) hj τ γ) L₁ L₂ →
    ∀ (f : Q.Mx k r → E) (Z : MJ j),
      (L₁.foldr (fun (T : (Q.Mx k r → E) → Q.Mx k r → E) (h : Q.Mx k r → E) => T h) f) (x0 k r j hj Z τ γ) =
      (L₂.foldr (fun (T : (MJ j → E) → MJ j → E) (h : MJ j → E) => T h) (fun Z' => f (x0 k r j hj Z' τ γ))) Z
  | [], [], _ => fun _ _ => rfl
  | T :: L₁, S :: L₂, List.Forall₂.cons h hL => by
    intro f Z
    simp only [List.foldr_cons]
    rw [h]
    congr 1
    funext Z'
    exact foldr_pull L₁ L₂ hL f Z'

theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) : ∀ (n : ℕ) (F : Fin n → α) (G : Fin n → β),
    (∀ i, R (F i) (G i)) → List.Forall₂ R (List.ofFn F) (List.ofFn G)
  | 0, _, _, _ => by simp
  | n + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn R n _ _ (fun i => h i.succ))

theorem qmin_pull (hC : CurveLevi) (hH : HpartLevi) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (hab : ∀ (σ : Equiv.Perm (Fin t)) (i : Fin t), Good k r j (a (σ i)) (b i)) (f : Q.Mx k r → E) (Z : MJ j) :
    qminorOp (EabH (Hpk k r)) a b u f (x0 k r j hj Z τ γ) =
      qminG (EopZ k r j) a b u (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold qminorOp qminG
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  congr 1
  refine foldr_pull hj τ γ _ _ ?_ f Z
  exact forall₂_ofFn (Rel (E := E) hj τ γ) t _ _ (fun i f' Z' => top_pull hj τ γ hC hH _ _ _ (hab σ i) f' Z')

theorem AAop_pull (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ)
    (f : Q.Mx k r → E) (Z : MJ j) :
    C3.AAop k r m hm u f (x0 k r j hj Z τ γ) = AZ k r j m hm hmj u (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  classical
  unfold C3.AAop AZ
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · have hcoef : (Matrix.of fun a l : Fin m =>
        herm (Hpk k r) (x0 k r j hj Z τ γ *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) =
        Matrix.of fun a l => cZ Z (c l) (Fin.castLE hmj a) := by
      ext a l
      exact hXC k r j hj Z τ γ (Fin.castLE hmj a) (c l)
    rw [hcoef]
    by_cases hall : ∀ l, (c l).val < j
    · rw [qmin_pull hj τ γ hC hH]
      intro σ i
      left
      exact ⟨by simp [C3.xR, eI]; omega, hall i⟩
    · push Not at hall
      obtain ⟨l, hl⟩ := hall
      rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [cZ]; omega)]
      simp
  · rfl

theorem AAvop_pull (hC : CurveLevi) (hH : HpartLevi) (hXV : XiCoefV) (m : ℕ) (hm : m ≤ r) (hmj : m ≤ j)
    (ell : ℂ) (f : Q.Mx k r → E) (Z : MJ j) (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) :
    C3.AAvop k r m hm ell f (x0 k r j hj Z τ γ) = AvZ k r j m hm hmj ell (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  classical
  unfold C3.AAvop AvZ
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · have hcoef : (Matrix.of fun a l : Fin m =>
        ((x0 k r j hj Z τ γ)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (c l)) =
        Matrix.of fun a l => cvZ k r Z (c l) (Fin.castLE hmj a) := by
      ext a l
      exact hXV k r j hj Z τ γ hZ hτ hγ (Fin.castLE hmj a) (c l)
    rw [hcoef]
    by_cases hall : ∀ l, 2 * r + k < (c l).val + j
    · rw [qmin_pull hj τ γ hC hH]
      intro σ i
      right
      have := i.isLt
      exact ⟨hall (σ i), by simp [C3.sR, esI]; omega⟩
    · push Not at hall
      obtain ⟨l, hl⟩ := hall
      rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [cvZ]; omega)]
      simp
  · rfl

theorem Dmin_pull (hXC : XiCoef) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : MJ j) :
    Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j, by omega⟩ = Z.det := by
  show ((Zhat k r z z' (x0 k r j hj Z τ γ)).submatrix (Fin.castLE (by omega : j ≤ r + 1))
    (Fin.castLE (by omega : j ≤ r + 1))).det = Z.det
  congr 1
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [Matrix.submatrix_apply, Zhat, fvec]
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
  have := hXC k r j hj Z τ γ a (eI k r ⟨b.val, by omega⟩)
  simp only [eI] at this ⊢
  simpa [hb] using this

theorem vLet_pull (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (hXV : XiCoefV)
    (z z' : Fin (2 * r + k + 1) → ℂ) (l : C.Letter) (e : Fin 2) (Φ : Q.Mx k r → E) (Z : MJ j)
    (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) :
    D.vLet k r z z' j (by omega) l e Φ (x0 k r j hj Z τ γ) =
      Aform k r j hj l e (fun Z' => Φ (x0 k r j hj Z' τ γ)) Z := by
  unfold D.vLet Aform
  split_ifs
  · rfl
  · rw [Dmin_pull hj τ γ hXC, AAop_pull hj τ γ hC hH hXC]
  · rw [Dmin_pull hj τ γ hXC, AAvop_pull hj τ γ hC hH hXV _ _ _ _ _ Z hZ hτ hγ]

end transfer

section lin

variable {j : ℕ}

def W (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Z : MJ j) : Submodule ℂ (MJ j → E) where
  carrier := {h | ∃ V : Set (MJ j), IsOpen V ∧ Z ∈ V ∧ ContDiffOn ℝ ∞ h V}
  add_mem' := by
    rintro h₁ h₂ ⟨V₁, o₁, m₁, s₁⟩ ⟨V₂, o₂, m₂, s₂⟩
    exact ⟨V₁ ∩ V₂, o₁.inter o₂, ⟨m₁, m₂⟩, (s₁.mono Set.inter_subset_left).add (s₂.mono Set.inter_subset_right)⟩
  zero_mem' := ⟨Set.univ, isOpen_univ, trivial, contDiffOn_const⟩
  smul_mem' := by
    rintro c h ⟨V, o, m, s⟩
    exact ⟨V, o, m, s.const_smul c⟩

def fW {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (Z : MJ j) (hZ : Z.det ≠ 0) : W E Z →ₗ[ℂ] E where
  toFun h := T h.1 Z
  map_add' := by
    rintro ⟨h₁, V₁, o₁, m₁, s₁⟩ ⟨h₂, V₂, o₂, m₂, s₂⟩
    exact hT.add (V₁ ∩ V₂ ∩ {Z | Z.det ≠ 0}) h₁ h₂ ((o₁.inter o₂).inter isOpen_inv)
      (fun _ h => h.2) (s₁.mono (fun _ h => h.1.1)) (s₂.mono (fun _ h => h.1.2)) Z ⟨⟨m₁, m₂⟩, hZ⟩
  map_smul' := by
    rintro c ⟨h, V, o, m, s⟩
    exact hT.smul (V ∩ {Z | Z.det ≠ 0}) c h (o.inter isOpen_inv) (fun _ h => h.2) (s.mono (fun _ h => h.1)) Z ⟨m, hZ⟩

def linOf {T : (MJ j → E) → MJ j → E} (hT : ZOp T) : (MJ j → E) →ₗ[ℂ] (MJ j → E) :=
  LinearMap.pi fun Z => if hZ : Z.det ≠ 0 then Classical.choose (LinearMap.exists_extend (fW hT Z hZ)) else 0

theorem linOf_eq {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {Z : MJ j} (hZ : Z.det ≠ 0) {h : MJ j → E}
    (hh : h ∈ W E Z) : linOf hT h Z = T h Z := by
  simp only [linOf, LinearMap.pi_apply, dif_pos hZ]
  have := Classical.choose_spec (LinearMap.exists_extend (fW hT Z hZ))
  exact congrArg (fun L : W E Z →ₗ[ℂ] E => L ⟨h, hh⟩) this

theorem dz_congr {F G : ℂ → E} {τ : ℂ} (h : F =ᶠ[𝓝 τ] G) : PBP.dz F τ = PBP.dz G τ := by
  unfold PBP.dz; rw [h.fderiv_eq]

theorem dzb_congr {F G : ℂ → E} {τ : ℂ} (h : F =ᶠ[𝓝 τ] G) : PBP.dzb F τ = PBP.dzb G τ := by
  unfold PBP.dzb; rw [h.fderiv_eq]

theorem linOf_par (hD : DzSlice) {T : (MJ j → E) → MJ j → E} (hT : ZOp T) : ParamComm (linOf hT) := by
  intro U κ hU hUi hκ
  obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
  have hsl : ∀ τ : ℂ, IsOpen {Z : MJ j | ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
    fun τ => hU.preimage (contDiff_pair τ).continuous
  have key : ∀ (τ : ℂ) (Z : MJ j), ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U →
      linOf hT (κ τ) Z = T (κ τ) Z := by
    intro τ Z hτZ
    exact linOf_eq hT (hUi hτZ) ⟨_, hsl τ, hτZ, hκ.comp (contDiff_pair τ).contDiffOn (fun _ h => h)⟩
  refine ⟨t1.congr (fun q hq => key q.1 (Matrix.of q.2) hq), fun q hq => ?_⟩
  have hev : (fun τ => linOf hT (κ τ) (Matrix.of q.2)) =ᶠ[𝓝 q.1] (fun τ => T (κ τ) (Matrix.of q.2)) := by
    have hop : IsOpen {τ : ℂ | ((τ, q.2) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (continuous_id.prodMk continuous_const)
    filter_upwards [hop.mem_nhds (show (q.1, q.2) ∈ U from hq)] with τ hτ
    exact key τ _ hτ
  obtain ⟨d1, d2⟩ := hD j E U κ hU hκ q.1
  refine ⟨?_, ?_⟩
  · rw [dz_congr hev, (t2 q hq).1]
    exact (linOf_eq hT (hUi hq) ⟨_, hsl q.1, hq, d1⟩).symm
  · rw [dzb_congr hev, (t2 q hq).2]
    exact (linOf_eq hT (hUi hq) ⟨_, hsl q.1, hq, d2⟩).symm

end lin

theorem zOnly_of_parts (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (hXV : XiCoefV) (hXM : XiMem)
    (hXS : XiSmooth) (hR : ZOpRd) (hD : DzSlice) : ZOnly := by
  intro k r j hj z z' E _ _ l e _ _
  refine ⟨linOf (zop_Aform (E := E) hR k r j hj l e), linOf_par hD _, ?_⟩
  intro Dm Φ _ _ hsm Z τ γ hZ hτ hγ hmem
  rw [vLet_pull hj τ γ hC hH hXC hXV z z' l e Φ Z hZ hτ hγ]
  refine (linOf_eq _ hZ ?_).symm
  obtain ⟨UF, F, hUF, hgUF, hF, hΦF⟩ := hsm _ ⟨hXM k r j hj Z τ γ hZ hτ hγ, hmem⟩
  have hcont := (hXS k r j hj τ γ).continuousOn
  refine ⟨{Z' | Z'.det ≠ 0} ∩ (fun Z' => x0 k r j hj Z' τ γ) ⁻¹' UF,
    hcont.isOpen_inter_preimage isOpen_inv hUF, ⟨hZ, hgUF⟩, ?_⟩
  refine (hF.comp ((hXS k r j hj τ γ).mono Set.inter_subset_left) (fun _ h => h.2)).congr ?_
  intro Z' hZ'
  exact hΦF _ hZ'.2 (hXM k r j hj Z' τ γ hZ'.1 hτ hγ)

end Formalism.FourierDecayAlt.P.WirtingerOperators
