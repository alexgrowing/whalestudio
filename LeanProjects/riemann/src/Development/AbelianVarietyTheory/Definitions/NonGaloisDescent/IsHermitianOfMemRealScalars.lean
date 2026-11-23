import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj

open Matrix

noncomputable section

namespace GlobalTheory.Tw

section Theta
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

def PhiGL (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R :=
  ⟨Phi n R, (Phi n R)ᵀ, Model.Phi_mul_transpose, Model.transpose_mul_Phi⟩

omit [StarRing R] in
@[simp] theorem PhiGL_val : (PhiGL n R).val = Phi n R := rfl

omit [StarRing R] in
@[simp] theorem PhiGL_inv_val : (PhiGL n R)⁻¹.val = (Phi n R)ᵀ := rfl

omit [StarRing R] in
theorem Phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_right_inv Model.Phi_mul_transpose

def thetaGL (g : GL (Fin n) R) : GL (Fin n) R := PhiGL n R * star g⁻¹ * (PhiGL n R)⁻¹

theorem thetaGL_val (g : GL (Fin n) R) : (thetaGL g).val = theta g.val := by
  simp [thetaGL, theta, Matrix.star_eq_conjTranspose, Phi_inv]

theorem thetaGL_thetaGL (g : GL (Fin n) R) : thetaGL (thetaGL g) = g :=
  Units.ext (by rw [thetaGL_val, thetaGL_val, Model.theta_theta g.isUnit])

theorem thetaGL_mul (g h : GL (Fin n) R) : thetaGL (g * h) = thetaGL g * thetaGL h :=
  Units.ext (by simp only [Units.val_mul, thetaGL_val, Model.theta_mul])

theorem star_PhiGL : star (PhiGL n R) = (PhiGL n R)⁻¹ :=
  Units.ext (by simp [Matrix.star_eq_conjTranspose, Model.Phi_conjTranspose, Phi_inv])

end Theta

structure PFlag (n : ℕ) (k : Type) [CommRing k] where

  carrier : Set (Submodule k (Fin n → k))
  chain : IsChain (· ≤ ·) carrier
  bot_mem : ⊥ ∈ carrier
  top_mem : ⊤ ∈ carrier

namespace PFlag

section Ring
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)

def triv (n : ℕ) (k : Type) [CommRing k] : PFlag n k where
  carrier := {⊥, ⊤}
  chain := by
    rintro _ (rfl | rfl) _ (rfl | rfl) _ <;> simp
  bot_mem := by simp
  top_mem := by simp

def single (V : Submodule k (Fin n → k)) : PFlag n k where
  carrier := {⊥, V, ⊤}
  chain := by
    rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) _ <;> simp
  bot_mem := by simp
  top_mem := by simp

def pred (V : Submodule k (Fin n → k)) : Submodule k (Fin n → k) := sSup {V' | V' ∈ F.carrier ∧ V' < V}

theorem pred_le (V : Submodule k (Fin n → k)) : F.pred V ≤ V := sSup_le fun _ h => h.2.le

theorem le_pred {V V' : Submodule k (Fin n → k)} (h : V' ∈ F.carrier) (hlt : V' < V) : V' ≤ F.pred V :=
  le_sSup ⟨h, hlt⟩

def lieQ : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact V.add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact V.smul_mem c (hX V hV v hv)

def lieN : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact (F.pred V).add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact (F.pred V).smul_mem c (hX V hV v hv)

variable {F}

theorem mem_lieQ {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieQ ↔ ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ V := Iff.rfl

theorem mem_lieN {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieN ↔ ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V := Iff.rfl

theorem lieN_le_lieQ : F.lieN ≤ F.lieQ := fun _ hX V hV v hv => F.pred_le V (hX V hV v hv)

theorem one_mem_lieQ : (1 : Matrix (Fin n) (Fin n) k) ∈ F.lieQ := fun V _ v hv => by simpa using hv

theorem mul_mem_lieQ {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (hY : Y ∈ F.lieQ) : X * Y ∈ F.lieQ :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact hX V hV _ (hY V hV v hv)

theorem mulVec_mem_pred {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (V : Submodule k (Fin n → k)) {v : Fin n → k}
    (hv : v ∈ F.pred V) : X *ᵥ v ∈ F.pred V := by
  have : F.pred V ≤ (F.pred V).comap X.mulVecLin :=
    sSup_le fun V' h w hw => F.le_pred h.1 h.2 (hX V' h.1 w hw)
  exact this hv

theorem lieQ_mul_lieN {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieQ) (hY : Y ∈ F.lieN) : X * Y ∈ F.lieN :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact mulVec_mem_pred hX V (hY V hV v hv)

theorem lieN_mul_lieQ {X Y : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) (hY : Y ∈ F.lieQ) : X * Y ∈ F.lieN :=
  fun V hV v hv => by rw [← mulVec_mulVec]; exact hX V hV _ (hY V hV v hv)

variable (F)

def stab : Subgroup (GL (Fin n) k) where
  carrier := {g | g.val ∈ F.lieQ ∧ g⁻¹.val ∈ F.lieQ}
  mul_mem' hg hh := ⟨mul_mem_lieQ hg.1 hh.1, by rw [_root_.mul_inv_rev]; exact mul_mem_lieQ hh.2 hg.2⟩
  one_mem' := ⟨one_mem_lieQ, one_mem_lieQ⟩
  inv_mem' hg := ⟨hg.2, hg.1⟩

def unip : Subgroup (GL (Fin n) k) where
  carrier := {g | g ∈ F.stab ∧ g.val - 1 ∈ F.lieN}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, by
    have : (g * h).val - 1 = (g.val - 1) * h.val + (h.val - 1) := by rw [Units.val_mul]; noncomm_ring
    rw [this]; exact add_mem (lieN_mul_lieQ hg.2 hh.1.1) hh.2⟩
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    have : g⁻¹.val - 1 = -(g⁻¹.val * (g.val - 1)) := by rw [mul_sub, Units.inv_mul]; simp
    rw [this]; exact neg_mem (lieQ_mul_lieN hg.1.2 hg.2)⟩

theorem unip_le_stab : F.unip ≤ F.stab := fun _ h => h.1

variable {F}

theorem mem_stab_iff_map {g : GL (Fin n) k} : g ∈ F.stab ↔ ∀ V ∈ F.carrier, V.map g.val.mulVecLin = V := by
  constructor
  · intro hg V hV
    refine le_antisymm ?_ fun v hv => ⟨g⁻¹.val *ᵥ v, hg.2 V hV v hv, by simp [mulVec_mulVec]⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hg.1 V hV v hv
  · intro h
    refine ⟨fun V hV v hv => (h V hV).le ⟨v, hv, rfl⟩, fun V hV v hv => ?_⟩
    obtain ⟨w, hw, rfl⟩ := (h V hV).ge hv
    simpa [mulVec_mulVec] using hw

theorem conj_mem_lieN {g : GL (Fin n) k} (hg : g ∈ F.stab) {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) :
    g.val * X * g⁻¹.val ∈ F.lieN := lieN_mul_lieQ (lieQ_mul_lieN hg.1 hX) hg.2

theorem conj_mem_unip {g u : GL (Fin n) k} (hg : g ∈ F.stab) (hu : u ∈ F.unip) : g * u * g⁻¹ ∈ F.unip :=
  ⟨mul_mem (mul_mem hg hu.1) (inv_mem hg), by
    have : (g * u * g⁻¹).val - 1 = g.val * (u.val - 1) * g⁻¹.val := by
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]; rfl
    rw [this]; exact conj_mem_lieN hg hu.2⟩

theorem lieQ_triv : (triv n k).lieQ = ⊤ := by
  refine eq_top_iff.2 fun X _ V hV v hv => ?_
  rcases hV with rfl | rfl
  · rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  · trivial

theorem stab_triv : (triv n k).stab = ⊤ := eq_top_iff.2 fun _ _ => by constructor <;> simp [lieQ_triv]

theorem mem_lieQ_single {V : Submodule k (Fin n → k)} {X : Matrix (Fin n) (Fin n) k} :
    X ∈ (single V).lieQ ↔ ∀ v ∈ V, X *ᵥ v ∈ V := by
  refine ⟨fun h => h V (by simp [single]), fun h V' hV' v hv => ?_⟩
  rcases hV' with rfl | rfl | rfl
  · rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  · exact h v hv
  · trivial

end Ring

section Field
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}

theorem mem_stab_iff {g : GL (Fin n) k} : g ∈ F.stab ↔ g.val ∈ F.lieQ := by
  refine ⟨fun h => h.1, fun h => mem_stab_iff_map.2 fun V hV => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact h V hV v hv) ?_
  refine (Submodule.equivMapOfInjective _ (fun v w hvw => ?_) V).finrank_eq.symm
  have := congrArg (g⁻¹.val *ᵥ ·) hvw
  simpa [mulVec_mulVec] using this

theorem mem_unip_iff {g : GL (Fin n) k} : g ∈ F.unip ↔ g.val - 1 ∈ F.lieN := by
  refine ⟨fun h => h.2, fun h => ⟨mem_stab_iff.2 ?_, h⟩⟩
  simpa using add_mem (lieN_le_lieQ h) one_mem_lieQ

theorem isNilpotent_of_mem_lieN {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) : IsNilpotent X := by
  have key : ∀ V : Submodule k (Fin n → k), V ∈ F.carrier → V ≤ Module.End.maxGenEigenspace (Matrix.toLin' X) 0 := by
    intro V
    induction V using WellFoundedLT.induction with
    | ind V ih =>
      intro hV v hv
      have h1 : F.pred V ≤ Module.End.maxGenEigenspace (Matrix.toLin' X) 0 := sSup_le fun V' h => ih V' h.2 h.1
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (h1 (hX V hV v hv))
      refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m + 1, ?_⟩
      simpa [pow_succ] using hm
  have h2 : IsNilpotent (Matrix.toLin' X) := Module.End.isNilpotent_iff_of_finite.2 fun v => by
    simpa using (Module.End.mem_maxGenEigenspace _ _ _).1 (key ⊤ F.top_mem (Submodule.mem_top (x := v)))
  exact (IsNilpotent.map_iff (f := Matrix.toLinAlgEquiv') Matrix.toLinAlgEquiv'.injective).1 h2

theorem pred_mem_and_lt {V : Submodule k (Fin n → k)} (hV : V ≠ ⊥) : F.pred V ∈ F.carrier ∧ F.pred V < V := by
  obtain ⟨M, hM, hmax⟩ := (wellFounded_gt (α := Submodule k (Fin n → k))).has_min {V' | V' ∈ F.carrier ∧ V' < V}
    ⟨⊥, F.bot_mem, bot_lt_iff_ne_bot.2 hV⟩
  have : F.pred V = M := le_antisymm (sSup_le fun V' h => by
    rcases F.chain.total h.1 hM.1 with h' | h'
    · exact h'
    · exact (eq_of_le_of_not_lt h' (hmax V' h)).ge) (le_sSup hM)
  rw [this]; exact hM

theorem mem_lieN_iff_trace {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieN ↔ ∀ Y ∈ F.lieQ, (X * Y).trace = 0 := by
  refine ⟨fun hX Y hY => (isNilpotent_trace_of_isNilpotent (isNilpotent_of_mem_lieN (lieN_mul_lieQ hX hY))).eq_zero,
    fun h V hV v hv => ?_⟩
  by_contra hn
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hY : ∀ w, LinearMap.toMatrix' (l.smulRight v) *ᵥ w = l w • v := fun w => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  have h1 := h (LinearMap.toMatrix' (l.smulRight v)) fun V' hV' w hw => by
    rw [hY]
    rcases F.chain.total hV hV' with h' | h'
    · exact V'.smul_mem _ (h' hv)
    · rcases h'.eq_or_lt with rfl | h''
      · exact V'.smul_mem _ hv
      · have : l w = 0 := by
          have : l w ∈ (F.pred V).map l := ⟨w, F.le_pred hV' h'' hw, rfl⟩
          rwa [hl0, Submodule.mem_bot] at this
        simp [this]
  apply hl
  rw [← h1, ← Matrix.trace_toLin'_eq, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  have : Matrix.toLin' X ∘ₗ l.smulRight v = l.smulRight (X *ᵥ v) := by ext; simp
  rw [this, LinearMap.trace_smulRight]

theorem mem_lieN_iff_trace_stab [Infinite k] {X : Matrix (Fin n) (Fin n) k} :
    X ∈ F.lieN ↔ ∀ g ∈ F.stab, (X * g.val).trace = 0 := by
  rw [mem_lieN_iff_trace]
  refine ⟨fun h g hg => h _ hg.1, fun h Y hY => ?_⟩
  obtain ⟨c, hc⟩ := (Matrix.finite_spectrum Y).exists_notMem
  obtain ⟨u, hu⟩ := spectrum.notMem_iff.1 hc
  have h1 := h u (mem_stab_iff.2 (by
    rw [hu, Algebra.algebraMap_eq_smul_one]; exact sub_mem (F.lieQ.smul_mem c one_mem_lieQ) hY))
  have h2 := h 1 (one_mem _)
  rw [hu, Algebra.algebraMap_eq_smul_one, mul_sub, trace_sub, Matrix.mul_smul, trace_smul] at h1
  rw [Units.val_one] at h2
  rwa [h2, smul_zero, zero_sub, neg_eq_zero] at h1

end Field

section Complex
variable {n : ℕ} (F : PFlag n ℂ)

theorem isClosed_lieQ : IsClosed (F.lieQ : Set (Matrix (Fin n) (Fin n) ℂ)) := F.lieQ.closed_of_finiteDimensional

theorem isClosed_lieN : IsClosed (F.lieN : Set (Matrix (Fin n) (Fin n) ℂ)) := F.lieN.closed_of_finiteDimensional

theorem isClosed_stab : IsClosed (F.stab : Set (GL (Fin n) ℂ)) :=
  (F.isClosed_lieQ.preimage Units.continuous_val).inter (F.isClosed_lieQ.preimage Units.continuous_coe_inv)

theorem isClosed_unip : IsClosed (F.unip : Set (GL (Fin n) ℂ)) :=
  F.isClosed_stab.inter (F.isClosed_lieN.preimage (Units.continuous_val.sub continuous_const))

end Complex

end PFlag

def perp {n : ℕ} (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {w | ∀ v ∈ V, w ⬝ᵥ star v = 0}
  add_mem' hw hw' v hv := by rw [add_dotProduct, hw v hv, hw' v hv, add_zero]
  zero_mem' v _ := by simp
  smul_mem' c w hw v hv := by rw [smul_dotProduct, hw v hv, smul_zero]

def PFlag.summand {n : ℕ} (F : PFlag n ℂ) (V : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) := V ⊓ perp (F.pred V)

section Perp
variable {n : ℕ}

theorem mulVec_dot_star (X : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    (X *ᵥ v) ⬝ᵥ star w = v ⬝ᵥ star (Xᴴ *ᵥ w) := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_comm v, ← dotProduct_mulVec, dotProduct_comm]

theorem dot_star_comm_zero {v w : Fin n → ℂ} (h : v ⬝ᵥ star w = 0) : w ⬝ᵥ star v = 0 := by
  have := congrArg star h
  rwa [star_zero, ← star_dotProduct_star, star_star] at this

theorem perp_anti {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp V' ≤ perp V := fun _ hw v hv => hw v (h hv)

open scoped ComplexOrder in
theorem eq_zero_of_dot_star {v : Fin n → ℂ} (h : v ⬝ᵥ star v = 0) : v = 0 := dotProduct_self_star_eq_zero.1 h

theorem eq_zero_of_mem_perp {V : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ} (h : v ∈ V) (h' : v ∈ perp V) : v = 0 :=
  eq_zero_of_dot_star (h' v h)

theorem sup_perp (V : Submodule ℂ (Fin n → ℂ)) : V ⊔ perp V = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨y, hy, w, hw, h⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := V.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap) (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin n))
  refine Submodule.mem_sup.2 ⟨y.ofLp, hy, w.ofLp, fun v hv => ?_, (congrArg WithLp.ofLp h).symm⟩
  have := hw (WithLp.toLp 2 v) hv
  rwa [EuclideanSpace.inner_eq_star_dotProduct] at this

theorem perp_perp (V : Submodule ℂ (Fin n → ℂ)) : perp (perp V) = V := by
  have h1 : V ≤ perp (perp V) := fun v hv w hw => dot_star_comm_zero (hw v hv)
  refine le_antisymm (fun z hz => ?_) h1
  obtain ⟨v, hv, u, hu, rfl⟩ := Submodule.mem_sup.1 ((sup_perp V).ge (Submodule.mem_top (x := z)))
  have : u = 0 := eq_zero_of_mem_perp hu (by simpa using sub_mem hz (h1 hv))
  simpa [this] using hv

namespace PFlag
variable {F : PFlag n ℂ}

theorem pred_sup_summand (F : PFlag n ℂ) (V : Submodule ℂ (Fin n → ℂ)) : F.pred V ⊔ F.summand V = V := by
  rw [summand, inf_comm, ← sup_inf_assoc_of_le _ (F.pred_le V), sup_perp, top_inf_eq]

theorem le_of_summand_le {U V : Submodule ℂ (Fin n → ℂ)} (hV : V ∈ F.carrier)
    (h : ∀ V' ∈ F.carrier, V' ≤ V → F.summand V' ≤ U) : V ≤ U := by
  induction V using WellFoundedLT.induction with
  | ind V ih =>
    rw [← F.pred_sup_summand V]
    exact sup_le (sSup_le fun V' h' => ih V' h'.2 h'.1 fun V'' h1 h2 => h V'' h1 (h2.trans h'.2.le)) (h V hV le_rfl)

theorem iSup_summand (F : PFlag n ℂ) : ⨆ V ∈ F.carrier, F.summand V = ⊤ :=
  top_le_iff.1 (le_of_summand_le F.top_mem fun V hV _ => le_iSup₂_of_le V hV le_rfl)

theorem summand_le_perp {V V' : Submodule ℂ (Fin n → ℂ)} (hV : V ∈ F.carrier) (h : V < V') : F.summand V' ≤ perp V :=
  inf_le_right.trans (perp_anti (F.le_pred hV h))

theorem mem_lieQ_and_star_iff {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ F.lieQ ∧ Xᴴ ∈ F.lieQ ↔ ∀ V ∈ F.carrier, ∀ v ∈ F.summand V, X *ᵥ v ∈ F.summand V := by
  constructor
  · rintro ⟨h1, h2⟩ V hV v hv
    exact ⟨h1 V hV v hv.1, fun w hw => by rw [mulVec_dot_star]; exact hv.2 _ (mulVec_mem_pred h2 V hw)⟩
  · intro h
    refine ⟨fun V hV => le_of_summand_le (U := V.comap X.mulVecLin) hV fun V' hV' hle v hv => hle (h V' hV' v hv).1,
      fun V hV v hv => ?_⟩
    rw [← perp_perp V]
    intro w hw
    have h1 : ⊤ ≤ V ⊔ (perp V ⊓ (perp V).comap X.mulVecLin) := le_of_summand_le F.top_mem fun V' hV' _ => by
      rcases F.chain.total hV' hV with h' | h'
      · exact le_sup_of_le_left (inf_le_left.trans h')
      · rcases h'.eq_or_lt with rfl | h''
        · exact le_sup_of_le_left inf_le_left
        · exact le_sup_of_le_right fun u hu => ⟨summand_le_perp hV h'' hu, summand_le_perp hV h'' (h V' hV' u hu)⟩
    obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 (h1 (Submodule.mem_top (x := w)))
    have h2 : y = 0 := eq_zero_of_mem_perp hy (by simpa using sub_mem hw hu.1)
    rw [h2, zero_add, mulVec_dot_star, conjTranspose_conjTranspose]
    exact dot_star_comm_zero (hu.2 v hv)

def realScalars (F : PFlag n ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ V ∈ F.carrier, ∃ c : ℝ, ∀ v ∈ F.summand V, X *ᵥ v = c • v}
  add_mem' hX hY V hV := by
    obtain ⟨c, hc⟩ := hX V hV
    obtain ⟨d, hd⟩ := hY V hV
    exact ⟨c + d, fun v hv => by rw [add_mulVec, hc v hv, hd v hv, add_smul]⟩
  zero_mem' V _ := ⟨0, fun v _ => by simp⟩
  smul_mem' r X hX V hV := by
    obtain ⟨c, hc⟩ := hX V hV
    exact ⟨r * c, fun v hv => by rw [smul_mulVec, hc v hv, mul_smul]⟩

theorem preserves_of_mem_realScalars {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ F.realScalars) :
    ∀ V ∈ F.carrier, ∀ v ∈ F.summand V, X *ᵥ v ∈ F.summand V := fun V hV v hv => by
  obtain ⟨c, hc⟩ := hX V hV
  rw [hc v hv]; exact (F.summand V).smul_of_tower_mem c hv

theorem isHermitian_of_mem_realScalars {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ F.realScalars) : X.IsHermitian := by
  have h0 := mem_lieQ_and_star_iff.2 (preserves_of_mem_realScalars hX)
  have h1 := (mem_lieQ_and_star_iff (X := Xᴴ)).1 ⟨h0.2, by simpa using h0.1⟩
  have h2 : ⊤ ≤ LinearMap.ker (Matrix.toLin' (Xᴴ - X)) := le_of_summand_le F.top_mem fun V hV _ v hv => by
    obtain ⟨c, hc⟩ := hX V hV
    have hd : (Xᴴ - X) *ᵥ v ∈ F.summand V := by
      rw [sub_mulVec]; exact sub_mem (h1 V hV v hv) (preserves_of_mem_realScalars hX V hV v hv)
    have h3 := hc _ hd
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    set d := (Xᴴ - X) *ᵥ v with hdef
    have h4 : d ⬝ᵥ star d = 0 := by
      conv_lhs => enter [1]; rw [hdef]
      rw [sub_mulVec, sub_dotProduct, mulVec_dot_star, conjTranspose_conjTranspose, h3, hc v hv]
      simp
    exact eq_zero_of_dot_star h4
  rw [top_le_iff, LinearMap.ker_eq_top, map_eq_zero_iff _ Matrix.toLin'.injective, sub_eq_zero] at h2
  exact h2

end PFlag

end Perp

theorem commute_of_commute_separable {n : ℕ} {A g h : Matrix (Fin n) (Fin n) ℂ} (hA : A.charpoly.Separable)
    (hg : Commute A g) (hh : Commute A h) : Commute g h := by
  set f := Matrix.toLin' A
  have hc : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' g) := hg.map Matrix.toLinAlgEquiv'
  have hfh : Commute f (Matrix.toLin' h) := hh.map Matrix.toLinAlgEquiv'
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤
      LinearMap.ker (Matrix.toLin' g * Matrix.toLin' h - Matrix.toLin' h * Matrix.toLin' g) := fun μ v hv => by
    have h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hc]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have hs : ∀ w ∈ Module.End.maxGenEigenspace f μ, ∃ c : ℂ, c • v = w := fun w hw => by
      have h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨w, hw⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    obtain ⟨c, hc⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv)
    obtain ⟨d, hd⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfh μ hv)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ← hc, ← hd, map_smul, map_smul,
      ← hc, ← hd, smul_comm, sub_self]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at h3
  exact Matrix.toLinAlgEquiv'.injective (by rw [map_mul, map_mul]; exact h3)

end GlobalTheory.Tw
