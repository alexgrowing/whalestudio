import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ExistsCond
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp.Key

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SplitFlip PositivityTheory.KCo

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section PartA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem acts_of_reads {v : Pl F} {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {S R}
    (h : Reads v ι S R) {j : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}
    (h2 : ∀ φ ∈ SB _, j (ι φ) = φ) {φ} (hφ : φ ∈ SB _) : j (R (ι φ)) ∈ SB _ ∧ Acts (evFin F v) S φ (j (R (ι φ))) := by
  obtain ⟨φ₁, a, b, c⟩ := h φ hφ
  rw [← c, h2 φ₁ a]
  exact ⟨a, b⟩

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem omB_right (ν α : kˣ →* ℂˣ) (h : GL (Fin d) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α 1 h Φ = ((α (gdet h) : ℂ) * apow (gdet h) ((n : ℂ) / 2)) • fun Y => Φ (Y * h.1) := funext fun Y => by
  simp [omB, gdet]

theorem omB_left (ν α : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α g 1 Φ = ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) • fun Y => Φ (g.1ᵀ * Y) := funext fun Y => by
  simp [omB, gdet]

def rH (h : GL (Fin d) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := Y * h.1
  invFun Y := Y * (h⁻¹).1
  left_inv Y := by simp [Matrix.mul_assoc]
  right_inv Y := by simp [Matrix.mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sb_right {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h : GL (Fin d) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (y * h.1)) ∈ SB _ :=
  ⟨hf.1.comp_continuous (rH h).continuous, hf.2.comp_homeomorph (rH h)⟩

def lH (g : GL (Fin n) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := g.1 * Y
  invFun Y := (g⁻¹).1 * Y
  left_inv Y := by simp [← Matrix.mul_assoc]
  right_inv Y := by simp [← Matrix.mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sb_left {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (g.1 * y)) ∈ SB _ :=
  ⟨hf.1.comp_continuous (lH g).continuous, hf.2.comp_homeomorph (lH g)⟩

end Loc

open scoped Classical

section Slot

variable {κ : Type} [Fintype κ]

def insertLocal (v : Pl F) (Φ : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ fun x => Φ (x - sgl v 1 • x)
  map_add' _ _ := funext fun _ => add_mul _ _ _
  map_smul' _ _ := funext fun _ => mul_assoc _ _ _

theorem insertLocal_acts {v : Pl F} {Φ : (κ → AF F) → ℂ} {S φ φ₁} (h : insertLocal v Φ φ ∈ schA F κ) (a : Acts (evFin F v) S φ φ₁) :
    S (insertLocal v Φ φ) = insertLocal v Φ φ₁ :=
  a _ ⟨fun x z hz => by simp only [smul_add, kd_at_iff.1 hz, add_sub_add_right_eq_sub], h⟩

theorem insertLocal_pure {v : Pl F} (f : SInf F κ) {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ}
    (h2 : ∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1)
    (hv : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (ψ) :
    insertLocal v (pure f φ) ψ = pure f (Function.update φ v ψ) := by
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h2
  have e : pure f φ = tens (evFin F v) (φ v) r := by rw [hr', Function.update_eq_self]
  have e2 : (fun x => pure f φ (x - sgl v 1 • x)) = r := funext fun x => by
    have h0 : (fun i => evFin F v ((x - sgl v 1 • x) i)) = 0 := funext fun i => by
      simp [ev_sgl]
    have h1 := hr (x - sgl v 1 • x) (sgl v 1 • x) (at_sgl_smul _ _)
    rw [sub_add_cancel] at h1
    rw [e, tens, h0, hv, Set.indicator_of_mem (by exact fun i => zero_mem _), Pi.one_apply, one_mul, h1]
  change tens _ _ _ = _
  rw [e2]
  exact hr' ψ

def slots (w : ∀ v : Pl F, (κ → Fv F v) → ℂ) (C : Submodule ℂ ((κ → AF F) → ℂ)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | ∀ᶠ v in cofinite, insertLocal v Φ (w v) = Φ ∧ ∀ φ ∈ SB (κ → Fv F v), insertLocal v Φ φ ∈ C}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]
    refine Eventually.of_forall fun v => ?_
    have : ∀ φ, insertLocal v (0 : (κ → AF F) → ℂ) φ = 0 := fun φ => funext fun _ => mul_zero _
    exact ⟨this _, fun φ _ => (this φ).symm ▸ zero_mem _⟩
  add_mem' := fun {a b} ha hb => by
    rw [Set.mem_ofPred_eq] at ha hb ⊢
    refine (ha.and hb).mono fun v h => ?_
    have : ∀ φ, insertLocal v (a + b) φ = insertLocal v a φ + insertLocal v b φ := fun φ => funext fun _ => mul_add _ _ _
    exact ⟨by rw [this, h.1.1, h.2.1], fun φ hφ => (this φ).symm ▸ add_mem (h.1.2 φ hφ) (h.2.2 φ hφ)⟩
  smul_mem' := fun c a ha => by
    rw [Set.mem_ofPred_eq] at ha ⊢
    refine ha.mono fun v h => ?_
    have : ∀ φ, insertLocal v (c • a) φ = c • insertLocal v a φ := fun φ => funext fun _ => mul_left_comm _ _ _
    exact ⟨by rw [this, h.1], fun φ hφ => (this φ).symm ▸ C.smul_mem c (h.2 φ hφ)⟩

theorem mem_placewise {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} {C : Submodule ℂ ((κ → AF F) → ℂ)} {Φ} :
    Φ ∈ slots w C ↔ ∀ᶠ v in cofinite, insertLocal v Φ (w v) = Φ ∧ ∀ φ ∈ SB (κ → Fv F v), insertLocal v Φ φ ∈ C := Iff.rfl

end Slot

variable {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem upd_sb {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _) {v : Pl F} {ψ}
    (hψ : ψ ∈ SB (Fin n × Fin d → Fv F v)) (u) : Function.update φ v ψ u ∈ SB _ := by
  by_cases hu : u = v
  · subst hu; rwa [Function.update_self]
  · rw [Function.update_of_ne hu]; exact h1 u

theorem upd_ev {φ w : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = w u) (v : Pl F)
    (ψ) : ∀ᶠ u in cofinite, Function.update φ v ψ u = w u := by
  filter_upwards [h, eventually_cofinite_ne v] with u h hu using (Function.update_of_ne hu _ _).trans h

theorem polData_le_placewise (hM : M.IsGood B.ψ) : PolData B M ≤ slots M.vac (PolData B M) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, φ, h1, h2, rfl⟩
  have h3 := (h2.and hM.std).mono fun _ h => h.1.trans h.2
  filter_upwards [h2, h3] with v a b
  refine ⟨by rw [insertLocal_pure f h3 b, ← a, Function.update_eq_self], fun ψ hψ => ?_⟩
  exact Submodule.subset_span ⟨f, hf, _, upd_sb h1 hψ, upd_ev h2 v ψ, insertLocal_pure f h3 b ψ⟩

theorem so_positions (hM : M.IsGood B.ψ) : M.So B.ψ B.τ₁ ≤ slots M.vac (M.So B.ψ B.τ₁) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, h4, rfl⟩
  have h3 := (h2.and hM.std).mono fun _ h => h.1.trans h.2
  filter_upwards [h2, h3, eventually_cofinite_ne B.v₁] with v a b c
  refine ⟨by rw [insertLocal_pure f h3 b, ← a, Function.update_eq_self], fun ψ hψ => ?_⟩
  exact Submodule.subset_span ⟨f, _, upd_sb h1 hψ, upd_ev h2 v ψ, by rwa [Function.update_of_ne c.symm], insertLocal_pure f h3 b ψ⟩

theorem polData_inf_so_le_placewise (hM : M.IsGood B.ψ) :
    PolData B M ⊓ M.So B.ψ B.τ₁ ≤ slots M.vac (PolData B M ⊓ M.So B.ψ B.τ₁) := fun _ h =>
  mem_placewise.2 (((mem_placewise.1 (polData_le_placewise hM h.1)).and (mem_placewise.1 (so_positions hM h.2))).mono
    fun _ k => ⟨k.1.1, fun φ hφ => ⟨k.1.2 φ hφ, k.2.2 φ hφ⟩⟩)

def apowH {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (z : ℂ) : kˣ →* ℂˣ :=
  MonoidHom.toHomUnits ⟨⟨fun x => apow x z, apow_one _⟩, fun x y => apow_mul x y _⟩

structure IsLoc {v : Pl F} (t : E →ₐ[F] Fv F v) (ξ α : (Fv F v)ˣ →* ℂˣ)
    (S : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) → UA σ W.J → ℂ) : Prop where
  aut : ∀ φ ∈ SB _, IsAut (W := W) (S φ)
  add : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, S (φ + φ') = S φ + S φ'
  smul : ∀ (c : ℂ) φ, S (c • φ) = c • S φ
  left : ∀ φ ∈ SB _, ∀ γ : GL (Fin n) (Fv F v), S (fun Y => φ (γ.1 * Y)) = (ξ (Matrix.GeneralLinearGroup.det γ) : ℂ) • S φ
  right : ∀ φ ∈ SB _, ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
    (fun x => S φ (x * h)) = (α (Matrix.GeneralLinearGroup.det h₀) : ℂ) • S fun Y => φ (Y * h₀.1)

theorem exists_loc (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {C : Submodule ℂ (Fn F n d)} (hs : C ≤ schA F _)
    (hc : ∀ Φ ∈ C, M.Conv om Φ) (ha : ∀ Φ ∈ C, IsAut (W := W) (M.I om Φ)) {Φ} (hΦ : Φ ∈ slots M.vac C) :
    ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, ∃ ι S, M.IsLinBar B.ψ t 1 1 ι ∧ ι (M.vac v) ∈ SB _ ∧
      IsLoc (W := W) t (chrW χW t * apowH ((d : ℂ) / 2))⁻¹ (chrW χX t * apowH ((n : ℂ) / 2)) S ∧ S (ι (M.vac v)) = M.I om Φ := by
  refine (mem_placewise.1 hΦ).mono fun v ⟨h0, hC⟩ t => ?_
  obtain ⟨⟨ι, hι⟩, s1, -, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v t
  obtain ⟨k1, k2⟩ := k ι hι
  obtain ⟨j, j1, j2⟩ := kd_exists_inv hι.bij
  have hv : M.vac v ∈ SB _ := (hp.good.vac v).1
  refine ⟨ι, fun φ => M.I om (insertLocal v Φ (j φ)), hι, hι.bij.1 hv, ⟨fun φ hφ => ha _ (hC _ (j1 φ hφ).1), fun φ hφ φ' hφ' => ?_,
    fun c φ => by simp only [map_smul, I_smul], fun φ hφ γ => ?_, fun φ hφ h hh h₀ e => ?_⟩, by simp only [j2 _ hv, h0]⟩
  · have a := hC _ (j1 φ hφ).1
    have b := hC _ (j1 φ' hφ').1
    funext h
    have e : ∀ g, theta om (insertLocal v Φ (j φ) + insertLocal v Φ (j φ')) g h =
        theta om (insertLocal v Φ (j φ)) g h + theta om (insertLocal v Φ (j φ')) g h := fun g => by
      simp only [theta, map_add]
      exact thetaSum_add F (hp.weil.isUSplitting.pres _ _ (hs a)) (hp.weil.isUSplitting.pres _ _ (hs b))
    simp only [map_add, Model.I, e, Pi.add_apply]
    exact integral_add (hc _ a h) (hc _ b h)
  · let g₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero γ.1ᵀ (by rw [Matrix.det_transpose]; exact γ.det_ne_zero)
    obtain ⟨g, hg, e⟩ := s1 g₀
    have a := hs (hC _ (j1 φ hφ).1)
    have b := insertLocal_acts a (acts_of_reads (k1 g hg g₀ e) j2 (j1 φ hφ).1).2
    have c := PositivityTheory.ThKF.I_left PositivityTheory.ThKF.unimodularity_holds hT hp a g
    rw [b, (j1 φ hφ).2, omB_left, map_smul, map_smul, I_smul,
      show gdet g₀ = Matrix.GeneralLinearGroup.det γ from Units.ext (Matrix.det_transpose _)] at c
    rw [← c, smul_smul]
    have : ((((chrW χW t * apowH ((d : ℂ) / 2))⁻¹ : (Fv F v)ˣ →* ℂˣ) (Matrix.GeneralLinearGroup.det γ) : ℂˣ) : ℂ) *
        ((chrW χW t (Matrix.GeneralLinearGroup.det γ) : ℂ) * apow (Matrix.GeneralLinearGroup.det γ) ((d : ℂ) / 2)) = 1 :=
      Units.inv_mul ((chrW χW t * apowH ((d : ℂ) / 2) : (Fv F v)ˣ →* ℂˣ) (Matrix.GeneralLinearGroup.det γ))
    rw [this, one_smul]
    rfl
  · have a := hs (hC _ (j1 φ hφ).1)
    have b := insertLocal_acts a (acts_of_reads (k2 h hh h₀ e) j2 (j1 φ hφ).1).2
    rw [← I_trans, b, (j1 φ hφ).2, omB_right, map_smul, map_smul, I_smul]
    rfl

end PartA

section PartB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d j : ℕ}
  {W : Spc F E d} {v : Pl F} {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

variable (t) in

def cp : UA σ W.J →* GL (Fin d) (Fv F v) := (Matrix.GeneralLinearGroup.map (piW t)).comp (Subgroup.subtype _)

theorem cp_val (g : UA σ W.J) : (cp t g).1 = (mat g).map (piW t) := rfl

theorem at_mul_l {z : AE F E} (h : At (evFin F v) z) (w : AE F E) : At (evFin F v) (w * z) :=
  fun u hu => by rw [← mul_smul_comm, h u hu, mul_zero]

theorem at_mul_r {z : AE F E} (h : At (evFin F v) z) (w : AE F E) : At (evFin F v) (z * w) := mul_comm w z ▸ at_mul_l h w

theorem uAt_mul {g k : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) (hk : k ∈ UAt σ W (evFin F v)) : g * k ∈ UAt σ W (evFin F v) := by
  have : mat (g * k) - 1 = mat g * (mat k - 1) + (mat g - 1) := by
    change mat g * mat k - 1 = _
    noncomm_ring
  change At _ _
  rw [this]
  exact (At.kd_mul_left hk _).kd_add hg

theorem uAt_one : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by
  change u • ((1 : Matrix (Fin d) (Fin d) (AE F E)) - 1) = 0
  rw [sub_self, smul_zero]

variable (v sec) in

def sA : Fv F v →+ AE F E := AddMonoidHom.mk' (fun x => sgl v x • sec (1, 0)) fun x y => by rw [map_add, add_smul]

theorem sA_at (x : Fv F v) : At (evFin F v) (sA v sec x) := at_sgl_smul _ _

theorem sA_cont : Continuous (sA v sec) :=
  (show Continuous (sgl v) from continuous_const.prodMk (continuous_singleFin v)).smul continuous_const

variable (h : IsSec σ t sec)
include h

theorem sA_fst (x : Fv F v) : piW t (sA v sec x) = x := by
  change piW t (sgl v x • sec (1, 0)) = _
  rw [(h.smul _ _).1, ev_sgl, h.fst, mul_one]

theorem sA_snd (x : Fv F v) : piW (t.comp σ) (sA v sec x) = 0 := by
  change piW (t.comp σ) (sgl v x • sec (1, 0)) = _
  rw [(h.smul _ _).2, h.snd, mul_zero]

theorem psi_ne {χ : AddChar (AE F E) ℂ} (hχ : IsChar σ χ) : χ.compAddMonoidHom (sA v sec) ≠ 1 := fun e => by
  obtain ⟨z, h1, h2, h3⟩ := hχ.2 v t
  have : z = sA v sec (piW t z) := sub_eq_zero.1 (h.ext _ (h1.kd_sub (sA_at _)) (by rw [map_sub, sA_fst h, sub_self])
    (by rw [map_sub, sA_snd h, h2, sub_self]))
  exact h3 (this ▸ DFunLike.congr_fun e (piW t z))

variable (hd : W.J.det ≠ 0)
include hd

theorem uJ : IsUnit ((incM F W.J).map (piW t)) := by
  rw [incM_map h]
  exact ((Matrix.isUnit_iff_isUnit_det W.J).2 hd.isUnit).map (t : E →+* Fv F v).mapMatrix

theorem snd_fix (g : UA σ W.J) (z : Fin d → Fv F v) (hz : ((cp t g).1ᵀ * W.J.map t) *ᵥ z = W.J.map t *ᵥ z) :
    (mat g).map (piW (t.comp σ)) *ᵥ z = z := by
  have a := h.unit_rel g
  have b : IsUnit ((cp t g).1ᵀ * W.J.map t) := ((Matrix.isUnit_transpose _).2 (cp t g).isUnit).mul (incM_map h W.J ▸ uJ h hd)
  rw [incM_map h] at a
  refine Matrix.mulVec_injective_iff_isUnit.2 b ?_
  rw [Matrix.mulVec_mulVec, hz]
  exact congrArg (· *ᵥ z) a

variable (hJ : ∀ a b, σ (W.J b a) = -W.J a b)
include hJ

theorem ex_at (g₀ : GL (Fin d) (Fv F v)) : ∃ g ∈ UAt σ W (evFin F v), cp t g = g₀ := by
  obtain ⟨g, h1, h2⟩ := h.exists_ug (J := incM F W.J) (ε := -1) (Matrix.ext fun a b => by
    rw [incM_map' h, incM_map h, neg_smul, one_smul, hJ, map_neg]; rfl) (uJ h hd) g₀
  exact ⟨g, h1, Units.ext h2⟩

theorem ex_split (g : UA σ W.J) : ∃ r, ∃ gv ∈ UAt σ W (evFin F v), cp t gv = cp t g ∧ g = r * gv ∧
    ∀ k ∈ UAt σ W (evFin F v), r * k = k * r := by
  obtain ⟨gv, h1, h2⟩ := ex_at h hd hJ (cp t g)
  refine ⟨g * gv⁻¹, gv, h1, h2, by group, fun k hk => ?_⟩
  have a : cp t (g * gv⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  generalize g * gv⁻¹ = r at a
  have a1 : (mat r).map (piW t) = 1 := congrArg Units.val a
  have a2 : (mat r).map (piW (t.comp σ)) = 1 :=
    Matrix.ext_of_mulVec_single fun i => by rw [snd_fix h hd r _ (by rw [a]; simp), Matrix.one_mulVec]
  refine Subtype.ext (Units.ext (h.extM (z := mat r * mat k) (z' := mat k * mat r) ?_ ?_ ?_))
  · rw [show mat r * mat k - mat k * mat r = mat r * (mat k - 1) - (mat k - 1) * mat r by noncomm_ring]
    exact (At.kd_mul_left hk _).kd_sub (At.kd_mul_right hk _)
  · rw [Matrix.map_mul, Matrix.map_mul, a1, one_mul, mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, a2, one_mul, mul_one]

omit hJ in
theorem transv {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) {x : Fin d → E} {w : Fin d → Fv F v}
    (e : (cp t g).1 = 1 + Matrix.vecMulVec (fun a => t (x a)) w) {z : Fin d → E} (hz : form σ W.J x z = 0) :
    mat g *ᵥ incV F z = incV F z + sA v sec (w ⬝ᵥ fun a => t (z a)) • incV F x := by
  have k : ∀ (π : AE F E →+* Fv F v) a, π ((mat g *ᵥ incV F z) a) = ((mat g).map π *ᵥ fun b => π (incV F z b)) a := fun π a =>
    RingHom.map_mulVec π _ _ a
  funext a
  refine sub_eq_zero.1 (h.ext _ ?_ ?_ ?_)
  · have : (mat g *ᵥ incV F z) a - (incV F z + sA v sec (w ⬝ᵥ fun a => t (z a)) • incV F x) a =
        ((mat g - 1) *ᵥ incV F z) a - sA v sec (w ⬝ᵥ fun a => t (z a)) * incV F x a := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    refine At.kd_sub (fun u hu => ?_) (at_mul_r (sA_at _) _)
    rw [← Pi.smul_apply, ← Matrix.smul_mulVec, hg u hu, Matrix.zero_mulVec, Pi.zero_apply]
  · rw [map_sub, k, ← cp_val, e]
    simp only [incV, (h.inc _).1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, sA_fst h, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_mul]
    ring
  · rw [map_sub, k, snd_fix h hd g]
    · simp only [incV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, sA_snd h, zero_mul, add_zero, sub_self]
    · have : (fun a => t (x a)) ⬝ᵥ W.J.map t *ᵥ (fun b => piW (t.comp σ) (incV F z b)) = 0 := by
        have := congrArg t hz
        simpa [form, dotProduct, Matrix.mulVec, incV, (h.inc _).2] using this
      rw [e, ← Matrix.mulVec_mulVec, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.vecMulVec_mulVec, this]
      simp

omit h hd in
theorem form_swap (hσ : ∀ x, σ (σ x) = x) {x z : Fin d → E} (e : form σ W.J z x = 0) : form σ W.J x z = 0 := by
  have a := congrArg σ e
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, map_zero, Finset.mul_sum] at a ⊢
  rw [Finset.sum_comm] at a
  rw [← neg_eq_zero, ← a, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

variable {u : Matrix (Fin d) (Fin j) E} {χ : AddChar (AE F E) ℂ} {Λ : (UA σ W.J → ℂ) → ℂ}

theorem wh_transv (hσ : ∀ x, σ (σ x) = x) (uu : uᵀ * W.J * u.map σ = 0) (hΛ : IsWh (σ := σ) W u χ Λ) {g : UA σ W.J}
    (hg : g ∈ UAt σ W (evFin F v)) {i i' : Fin j} (hi : (i' : ℕ) = i + 1) {w : Fin d → Fv F v}
    (e : (cp t g).1 = 1 + Matrix.vecMulVec (fun a => t (u a i)) w) (hw : ∀ b ≤ i, (w ⬝ᵥ fun a => t (u a b)) = 0)
    {f} (hf : IsAut (W := W) f) : Λ (fun x => f (x * g)) = χ (sA v sec (w ⬝ᵥ fun a => t (u a i'))) * Λ f := by
  have k := hΛ.law f hf g (1 + Matrix.of fun a b => if a = i then sA v sec (w ⬝ᵥ fun a => t (u a b)) else 0) ?_ ?_ ?_ ?_
  · rw [k, Finset.sum_eq_single (i, i')]
    · have : i ≠ i' := fun e => by rw [e] at hi; omega
      simp [this]
    · rintro ⟨a, b⟩ hab hne
      have h1 : (b : ℕ) = a + 1 := by simpa using hab
      have h2 : a ≠ b := fun e => by rw [e] at h1; omega
      have h3 : a ≠ i := fun e => hne (Prod.ext e (Fin.ext (show (b : ℕ) = i' by rw [e] at h1; omega)))
      simp [h2, h3]
    · intro hn
      exact absurd (by simpa using hi) hn
  · ext a b
    have := congrFun (transv h hd hg (x := fun a => u a i) e (z := fun a => u a b) (by
      have := congrFun (congrFun uu i) b
      rw [Matrix.mul_assoc] at this
      exact this)) a
    refine this.trans ?_
    rw [Matrix.mul_add, Matrix.mul_one]
    simp [Matrix.mul_apply, incV, incM, mul_comm]
  · intro a b hb
    by_cases ha : a = i
    · subst ha; simp [hw b hb.le, hb.ne']
    · simp [ha, hb.ne']
  · intro a
    by_cases ha : a = i
    · subst ha; simp [hw a le_rfl]
    · simp [ha]
  · intro z hz
    have m : (fun a => u a i) ∈ colSp u := Submodule.subset_span ⟨i, rfl⟩
    rw [transv h hd hg e (form_swap hJ hσ (hz _ m)), add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, m, rfl⟩)

omit h hd hJ in
theorem aut_right {f : UA σ W.J → ℂ} (hf : IsAut (W := W) f) (r : UA σ W.J) : IsAut (W := W) fun x => f (x * r) :=
  ⟨hf.1.comp (continuous_mul_const r), fun γ hγ x => by simp only [mul_assoc, hf.2 γ hγ]⟩

theorem exists_l (hσ : ∀ x, σ (σ x) = x) (uu : uᵀ * W.J * u.map σ = 0) (hΛ : IsWh (σ := σ) W u χ Λ) {ξ α S}
    (hS : IsLoc (n := n) (σ := σ) (W := W) t ξ α S) {e : Fin j → Fin d} {c : GL (Fin d) (Fv F v)} (hc : ∀ a i, c.1 a (e i) = t (u a i))
    (g : UA σ W.J) : ∃ l : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ, LeftLaw ξ l ∧
      (∀ i i' : Fin j, (i' : ℕ) = i + 1 → ∀ T : Set (Fin d), (∀ b ≤ i, e b ∈ T) →
        ColLaw (χ.compAddMonoidHom (sA v sec)) T (e i) (e i') l) ∧
      ∀ k ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, Λ (fun x => S φ (x * (k * g))) =
        α (Matrix.GeneralLinearGroup.det (cp t k * cp t g)) * l fun Y => φ (Y * (c⁻¹ * (cp t k * cp t g)).1) := by
  obtain ⟨r, gv, hv, e1, e2, hr⟩ := ex_split h hd hJ g
  let L : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => Λ fun x => S (fun Y => φ.1 (Y * c.1)) (x * r)
      map_add' := fun φ φ' => by
        rw [← hΛ.add _ _ (aut_right (hS.aut _ (sb_right φ.2 c)) r) (aut_right (hS.aut _ (sb_right φ'.2 c)) r)]
        exact congrArg (fun f : UA σ W.J → ℂ => Λ fun x => f (x * r)) (hS.add _ (sb_right φ.2 c) _ (sb_right φ'.2 c))
      map_smul' := fun a φ =>
        (congrArg (fun f : UA σ W.J → ℂ => Λ fun x => f (x * r)) (hS.smul a fun Y => φ.1 (Y * c.1))).trans (hΛ.smul a _) }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L
  have hl' : ∀ φ ∈ SB _, l φ = Λ fun x => S (fun Y => φ (Y * c.1)) (x * r) := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun φ hφ γ => ?_, fun i i' hi T hT φ hφ ρ hρ => ?_, fun k hk φ hφ => ?_⟩
  · rw [hl' _ (sb_left hφ γ), hl' _ hφ, ← hΛ.smul]
    have := hS.left _ (sb_right hφ c) γ
    simp only [Matrix.mul_assoc] at this
    rw [this]
    rfl
  · have d1 : (1 + Matrix.vecMulVec (Pi.single (e i) 1) ρ).det = 1 := by
      rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
      simp [hρ _ (hT i le_rfl)]
    let N := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (d1.trans_ne one_ne_zero)
    have hN : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), colOp (e i) ρ Y = Y * N.1 := fun Y => by
      change _ = Y * (1 + _)
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_single_one]
      rfl
    obtain ⟨k, hk, ek⟩ := ex_at h hd hJ (c * N * c⁻¹)
    have cu : ∀ b, (fun a => t (u a b)) = c.1 *ᵥ Pi.single (e b) 1 := fun b => by
      rw [Matrix.mulVec_single_one]; exact funext fun a => (hc a b).symm
    have hw : ∀ b, ((ρ ᵥ* (c⁻¹).1) ⬝ᵥ fun a => t (u a b)) = ρ (e b) := fun b => by
      rw [cu, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, dotProduct_single, mul_one]
    have a := wh_transv h hd hJ hσ uu hΛ hk hi (w := ρ ᵥ* (c⁻¹).1) (by
      rw [ek, cu]
      change c.1 * (1 + _) * (c⁻¹).1 = _
      rw [mul_add, add_mul, mul_one, Units.mul_inv, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul])
      (fun b hb => by rw [hw, hρ _ (hT b hb)]) (aut_right (hS.aut _ (sb_right hφ c)) r)
    have b := hS.right _ (sb_right hφ c) k hk _ (congrArg Units.val ek)
    rw [show Matrix.GeneralLinearGroup.det (c * N * c⁻¹) = 1 by
      rw [map_mul, map_mul, map_inv, show Matrix.GeneralLinearGroup.det N = 1 from Units.ext d1, mul_one, mul_inv_cancel],
      map_one, Units.val_one, one_smul] at b
    simp only [hN]
    rw [hl' _ (sb_right hφ N), hl' _ hφ, AddChar.compAddMonoidHom_apply, ← hw, ← a]
    congr 1
    funext x
    rw [mul_assoc, ← hr k hk, ← mul_assoc, congrFun b]
    simp [Matrix.mul_assoc]
  · rw [hl' _ (sb_right hφ _), ← hΛ.smul]
    congr 1
    funext x
    have b := congrFun (hS.right _ hφ _ (uAt_mul hk hv) (cp t k * cp t g) (by rw [← e1, ← map_mul]; rfl)) (x * r)
    rw [show x * (k * g) = x * r * (k * gv) by rw [e2, ← mul_assoc k, ← hr k hk, mul_assoc, mul_assoc], b]
    simp [Matrix.mul_assoc]

end PartB

section PartC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d j : ℕ}
  {W : Spc F E d} {v : Pl F} {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

theorem wh_sub {u : Matrix (Fin d) (Fin j) E} {χ Λ} (hΛ : IsWh (σ := σ) W u χ Λ) {f f' : UA σ W.J → ℂ} (hf : IsAut (W := W) f)
    (hf' : IsAut (W := W) f') (g : UA σ W.J) :
    Λ (fun x => (f - f') (x * g)) = Λ (fun x => f (x * g)) - Λ fun x => f' (x * g) := by
  have a : IsAut (W := W) (f - f') := by simpa using isAut_sub hf hf' 1
  rw [eq_sub_iff_add_eq, ← hΛ.add _ _ (aut_right a g) (aut_right hf' g)]
  congr 1
  funext x
  simp

theorem frame_compl {u u' : Matrix (Fin d) (Fin j) E} (hu : IsFrame σ W u u') :
    ∃ (e : Fin j → Fin d) (c : GL (Fin d) E), Function.Injective e ∧ (∀ a i, c.1 a (e i) = u a i) ∧
      (W.J * u'.map σ)ᵀ * c.1 = (1 : Matrix (Fin d) (Fin d) E).submatrix e id :=
  exists_compl u _ (by rw [← Matrix.transpose_transpose u, ← Matrix.transpose_mul, ← Matrix.mul_assoc, hu.uv, Matrix.transpose_one])

section Triple

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

open PositivityTheory.ThKG in
theorem locV (hB : ThetaBasic) (hK : KDecay) (hA : IAut) (hT : IsTriple B G X om om') {Φ} (hΦ : Φ ∈ PolData B G.M) :
    ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, ∃ ι S, G.M.IsLinBar B.ψ t 1 1 ι ∧ ι (G.M.vac v) ∈ SB _ ∧
      IsLoc (W := G.W) t (chrW (X.β / X.α) t * apowH (((a + a' : ℕ) : ℂ) / 2))⁻¹ (chrW X.β t * apowH ((a : ℂ) / 2)) S ∧
        S (ι (G.M.vac v)) = G.M.I om Φ :=
  exists_loc hB (pairV hT) (polData_le hT.geo.hM) (fun Φ h => (hK F E σ B a a' G X om om' hT).1 Φ (polData_le hT.geo.hM h))
    (hA F E σ B a a' G X om om' hT).1 (polData_le_placewise hT.geo.hM hΦ)

open PositivityTheory.ThKG in
theorem locV' (hB : ThetaBasic) (hK : KDecay) (hA : IAut) (hT : IsTriple B G X om om') {Φ}
    (hΦ : Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) :
    ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, ∃ ι S, G.M'.IsLinBar B.ψ t 1 1 ι ∧ ι (G.M'.vac v) ∈ SB _ ∧
      IsLoc (W := G.W) t (chrW (X.α / X.β) t * apowH (((a + a' : ℕ) : ℂ) / 2))⁻¹ (chrW X.α t * apowH ((a' : ℂ) / 2)) S ∧
        S (ι (G.M'.vac v)) = G.M'.I om' Φ :=
  exists_loc hB (pairV' hT) (inf_le_left.trans (polData_le hT.geo.hM')) (fun Φ h => ((hK F E σ B a a' G X om om' hT).2 Φ h.2).2.1)
    (hA F E σ B a a' G X om om' hT).2 (polData_inf_so_le_placewise hT.geo.hM' hΦ)

end Triple

theorem three (hL : LocThree) (h : IsSec σ t sec) (hd : W.J.det ≠ 0) (hJ : ∀ a b, σ (W.J b a) = -W.J a b) (hσ : ∀ x, σ (σ x) = x)
    {u u' : Matrix (Fin d) (Fin (j + 3)) E} (hu : IsFrame σ W u u') {χ Λ} (hχ : IsChar σ χ) (hΛ : IsWh (σ := σ) W u χ Λ) {ξ α S}
    (hS : IsLoc (n := n) (σ := σ) (W := W) t ξ α S) {φ} (hφ : φ ∈ SB _) (g : UA σ W.J) : Λ (fun x => S φ (x * g)) = 0 := by
  obtain ⟨e, c, he, hc, -⟩ := frame_compl hu
  obtain ⟨l, l1, l2, l3⟩ := exists_l h hd hJ hσ hu.uu hΛ hS (e := e) (c := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) c)
    (fun a i => congrArg t (hc a i)) g
  have := l3 1 uAt_one φ hφ
  rw [one_mul, hL _ n d _ (psi_ne h hχ) (e ⟨0, by omega⟩) (e ⟨1, by omega⟩) (e ⟨2, by omega⟩) (he.ne (by simp)) (he.ne (by simp))
    (he.ne (by simp)) ξ l l1 (l2 _ _ rfl _ fun b hb => ?_) (l2 _ _ rfl _ fun b hb => ?_) _ (sb_right hφ _), mul_zero] at this
  · exact this
  · exact congrArg e (Fin.ext (Nat.le_zero.1 hb))
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (show (b : ℕ) ≤ 1 from hb) with hb | hb
    exacts [Or.inl (congrArg e (Fin.ext hb)), Or.inr (congrArg e (Fin.ext hb))]

theorem keyThree_of_locThree (hB : ThetaBasic) (hK : KDecay) (hA : IAut) (hL : LocThree) (hP : Places) : KeyThree := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' hT j u u' hu χ Λ hχ hΛ _ ⟨Φ, hΦ, Φ', hΦ', rfl⟩ g
  obtain ⟨v, ⟨t⟩, h1, h2⟩ := ((frequently_cofinite_iff_infinite.2 (hP F E σ hT.base.cm).2.2.2).and_eventually
    ((locV hB hK hA hT hΦ).and (locV' hB hK hA hT hΦ'))).exists
  obtain ⟨ι, S, -, a1, a2, a3⟩ := h1 t
  obtain ⟨ι', S', -, b1, b2, b3⟩ := h2 t
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hT.base.cm v t
  have hd := PositivityTheory.ThKF.detW (PositivityTheory.ThKG.pairV hT)
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  rw [← a3, ← b3, wh_sub hΛ (a2.aut _ a1) (b2.aut _ b1), three hL h hd hT.geo.hW.skew hσ hu hχ hΛ a2 a1,
    three hL h hd hT.geo.hW.skew hσ hu hχ hΛ b2 b1, sub_self]

theorem det_torus {k : Type} [Field k] {i₀ i₁ : Fin d} (hi : i₀ ≠ i₁) {x : k} (hx : x ≠ 0) :
    (Matrix.diagonal fun i => if i = i₀ then x else if i = i₁ then x⁻¹ else 1).det = 1 := by
  rw [Matrix.det_diagonal, Finset.prod_congr rfl (g := fun i => (if i = i₀ then x else 1) * if i = i₁ then x⁻¹ else 1) fun i _ => ?_,
    Finset.prod_mul_distrib]
  · simp [hx]
  · by_cases h0 : i = i₀
    · subst h0; simp [hi]
    · simp [h0]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem torus_eq {e : Fin 2 → Fin d} (h01 : e 0 ≠ e 1) (x : k) : torus (e 0) (e 1) x =
    1 + (1 : Matrix (Fin d) (Fin d) k).submatrix id e * (!![x, 0; 0, x⁻¹] - 1) * (1 : Matrix (Fin d) (Fin d) k).submatrix e id := by
  ext a b
  simp only [torus, Matrix.diagonal_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.one_apply, id]
  by_cases a0 : a = e 0
  · subst a0
    by_cases b0 : e 0 = b
    · subst b0; simp [h01, h01.symm]
    · simp [b0, h01]
  by_cases a1 : a = e 1
  · subst a1
    by_cases b0 : e 1 = b
    · subst b0; simp [h01, h01.symm]
    · simp [b0, a0]
  · simp [a0, a1]

theorem oneO_tor {c x g : GL (Fin d) k} {T : Matrix (Fin d) (Fin d) k} (a : (c⁻¹ * x * c).1 = T) (ci : IntM c.1) (ci' : IntM (c⁻¹).1)
    (gi : IntM g.1) (gi' : IntM (g⁻¹).1) (Y : Matrix (Fin n) (Fin d) k) :
    oneO k n d (Y * (c⁻¹ * (x * g)).1) = oneO k n d (Y * T) := by
  rw [show c⁻¹ * (x * g) = c⁻¹ * x * c * (c⁻¹ * g) by group, Units.val_mul _ (c⁻¹ * g), a, ← Matrix.mul_assoc]
  refine oneO_mul (ci'.mul gi) ?_ _
  rw [mul_inv_rev, inv_inv]
  exact gi'.mul ci

end Loc

theorem exists_torus (h : IsSec σ t sec) {u u' : Matrix (Fin d) (Fin 2) E} {m} (hm : IsLev (σ := σ) (W := W) u u' m)
    {e : Fin 2 → Fin d} {c : GL (Fin d) E} (he : Function.Injective e) (hc : ∀ a i, c.1 a (e i) = u a i)
    (hp : (W.J * u'.map σ)ᵀ * c.1 = (1 : Matrix (Fin d) (Fin d) E).submatrix e id) (x : (Fv F v)ˣ) :
    ∃ b : GL (Fin 2) (AE F E), (x = 1 → b = 1) ∧ Matrix.GeneralLinearGroup.det b = 1 ∧ m b ∈ UAt σ W (evFin F v) ∧
      (cp t (m b)).1 * c.1.map t = c.1.map t * torus (e 0) (e 1) (x : Fv F v) := by
  obtain ⟨b, b0, b1, b2⟩ := h.exists_gl (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(x : Fv F v), 0; 0, (x : Fv F v)⁻¹] (by simp)) 1
  replace b1 : b.1.map (piW t) = !![(x : Fv F v), 0; 0, (x : Fv F v)⁻¹] := b1
  replace b2 : b.1.map (piW (t.comp σ)) = 1 := b2
  have i0 : At (evFin F v) ((b⁻¹).1 - 1) := by
    have : (b⁻¹).1 - 1 = -(b⁻¹).1 * (b.1 - 1) := by rw [neg_mul, mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [this]
    exact At.kd_mul_left b0 _
  have i2 : (b⁻¹).1.map (piW (t.comp σ)) = 1 := by
    have := congrArg (fun z : Matrix (Fin 2) (Fin 2) (AE F E) => z.map (piW (t.comp σ))) b.inv_mul
    simp only [Matrix.map_mul, b2, mul_one] at this
    exact this.trans (Matrix.map_one _ (map_zero _) (map_one _))
  refine ⟨b, fun hx => Units.ext (h.extM b0 ?_ ?_), Units.ext (sub_eq_zero.1 (h.ext _ ?_ ?_ ?_)), ?_, ?_⟩
  · rw [b1, hx, Units.val_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.one_fin_two]
  · rw [b2, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · have k := kd_at_matrix.1 b0
    have : ((Matrix.GeneralLinearGroup.det b : (AE F E)ˣ) : AE F E) - (1 : (AE F E)ˣ) =
        (b.1 - 1) 0 0 * b.1 1 1 + (b.1 - 1) 1 1 - (b.1 - 1) 0 1 * b.1 1 0 := by
      change b.1.det - 1 = _
      simp [Matrix.det_fin_two]; ring
    rw [this]
    exact ((at_mul_r (k 0 0) _).kd_add (k 1 1)).kd_sub (at_mul_r (k 0 1) _)
  · change piW t (b.1.det - 1) = 0
    rw [map_sub, RingHom.map_det, RingHom.mapMatrix_apply, b1]; simp
  · change piW (t.comp σ) (b.1.det - 1) = 0
    rw [map_sub, RingHom.map_det, RingHom.mapMatrix_apply, b2]; simp
  · change At _ _
    rw [hm.2, levM, add_sub_assoc, add_sub_cancel_left]
    refine ((At.kd_mul_left b0 _).kd_mul_right _).kd_sub ((At.kd_mul_left ?_ _).kd_mul_right _)
    rw [← Matrix.transpose_one, ← Matrix.transpose_sub, ← Matrix.map_one (cA σ) (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub _)]
    exact At.kd_transpose (kd_at_matrix.2 fun i j => h.atConj _ (kd_at_matrix.1 i0 i j))
  · have hp' : ((W.J * u'.map σ)ᵀ).map t * c.1.map t = (1 : Matrix (Fin d) (Fin d) (Fv F v)).submatrix e id := by
      rw [← Matrix.map_mul, hp]
      ext a b
      simp [Matrix.one_apply, apply_ite t]
    have hu : u.map t = c.1.map t * (1 : Matrix (Fin d) (Fin d) (Fv F v)).submatrix id e := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, hc]
    have z : (((b⁻¹).1.map (cA σ))ᵀ).map (piW t) = 1 := by rw [Matrix.transpose_map, h.conj1, i2, Matrix.transpose_one]
    rw [cp_val, hm.2, levM, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), z, b1,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      sub_self, Matrix.mul_zero, Matrix.zero_mul, sub_zero, incM_map h, incM_map h,
      torus_eq (he.ne (by simp)), add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc _ _ (c.1.map t), hp', hu]
    simp only [Matrix.mul_assoc]

theorem two (hL : LocTwo) (h : IsSec σ t sec) (hd : W.J.det ≠ 0) (hJ : ∀ a b, σ (W.J b a) = -W.J a b) (hσ : ∀ x, σ (σ x) = x)
    {u u' : Matrix (Fin d) (Fin 2) E} (hu : IsFrame σ W u u') {χ Λ} (hΛ : IsWh (σ := σ) W u χ Λ) {ξ α S}
    (hS : IsLoc (n := n) (σ := σ) (W := W) t ξ α S) {φ} (hφ : φ ∈ SB _) {κ : ℂ} (e0 : φ = κ • oneO (Fv F v) n d)
    (hξ : ∀ x : (Fv F v)ˣ, ValuativeRel.valuation _ (x : Fv F v) = 1 → ξ x = 1) {ϖ : (Fv F v)ˣ} (hϖ : IsUnif ϖ) {c₀ : ℤ}
    (c1 : ∀ x, ValuativeRel.valuation _ x ≤ ValuativeRel.valuation _ ((ϖ ^ c₀ : (Fv F v)ˣ) : Fv F v) →
      χ.compAddMonoidHom (sA v sec) x = 1)
    (c2 : ∃ x, ValuativeRel.valuation _ x ≤ ValuativeRel.valuation _ ((ϖ ^ (c₀ - 1) : (Fv F v)ˣ) : Fv F v) ∧
      χ.compAddMonoidHom (sA v sec) x ≠ 1)
    {e : Fin 2 → Fin d} (he : Function.Injective e) {c : GL (Fin d) (Fv F v)} (hc : ∀ a i, c.1 a (e i) = t (u a i))
    (ci : IntM c.1) (ci' : IntM (c⁻¹).1) {k : ℕ → UA σ W.J} (hk : ∀ i, k i ∈ UAt σ W (evFin F v))
    (hk' : ∀ i, (cp t (k i)).1 * c.1 = c.1 * torus (e 0) (e 1) ((ϖ : Fv F v) ^ i)) {g : UA σ W.J} (gi : IntM (cp t g).1)
    (gi' : IntM (cp t g⁻¹).1) : ∃ x : ℂ, ∀ i, Λ (fun z => S φ (z * (k i * g))) =
      x * yy (GlobalTheory.SplitWeil.resCard (Fv F v)) (ξ ϖ * (GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ ((n : ℤ) - d)) c₀ i := by
  obtain ⟨l, l1, l2, l3⟩ := exists_l h hd hJ hσ hu.uu hΛ hS hc g
  have h01 : e 0 ≠ e 1 := he.ne (by simp)
  obtain ⟨x, hx⟩ := hL _ n d ϖ hϖ _ c₀ c1 c2 _ _ h01 ξ hξ l l1
    (l2 0 1 rfl _ fun b hb => congrArg e (Fin.ext (Nat.le_zero.1 hb))) _ rfl
  refine ⟨α (Matrix.GeneralLinearGroup.det (cp t g)) * κ * x, fun i => ?_⟩
  have a : (c⁻¹ * cp t (k i) * c).1 = torus (e 0) (e 1) ((ϖ : Fv F v) ^ i) := by
    rw [Units.val_mul, Units.val_mul, mul_assoc, hk', Units.inv_mul_cancel_left]
  have b : Matrix.GeneralLinearGroup.det (cp t (k i)) = 1 := by
    have : Matrix.GeneralLinearGroup.det (c⁻¹ * cp t (k i) * c) = 1 :=
      Units.ext ((congrArg Matrix.det a).trans (det_torus h01 (pow_ne_zero _ ϖ.ne_zero)))
    rwa [map_mul, map_mul, map_inv, inv_mul_cancel_comm] at this
  have o : (fun Y : Matrix (Fin n) (Fin d) (Fv F v) => φ (Y * (c⁻¹ * (cp t (k i) * cp t g)).1)) =
      κ • fun Y : Matrix (Fin n) (Fin d) (Fv F v) => oneO (Fv F v) n d (Y * torus (e 0) (e 1) ((ϖ : Fv F v) ^ i)) := funext fun Y => by
    rw [e0, Pi.smul_apply, Pi.smul_apply, oneO_tor a ci ci' gi (by rwa [← map_inv])]
  rw [l3 _ (hk i) φ hφ, o, map_smul, hx, map_mul, b, one_mul, yy, smul_eq_mul]
  ring

theorem chrW_div (χ χ' : Chr F E) (x : (Fv F v)ˣ) : chrW (χ / χ') t x = chrW χ t x / chrW χ' t x := map_div Circle.toUnits _ _

theorem keyTwo_of_locTwo_vacBar (hB : ThetaBasic) (hK : KDecay) (hA : IAut) (hL : LocTwo) (hV : VacBar) (hP : Places) : KeyTwo := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' hT u u' hu m hm χ Λ hχ hΛ _ ⟨Φ, hΦ, Φ', hΦ', rfl⟩ h₀
  obtain ⟨p1, p2, p3, p4⟩ := hP F E σ hT.base.cm
  obtain ⟨e, c, he, hc, hp⟩ := frame_compl hu
  have im : ∀ z : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, IntM (z.map (piW t)) :=
    fun z => (eventually_all.2 fun i => eventually_all.2 fun j => p2 (z i j)).mono fun v h t i j => h i j t
  obtain ⟨v, ⟨t⟩, ⟨h1, h2⟩, ⟨v1, v2⟩, ⟨i1, i2⟩, ⟨i3, i4⟩, hv⟩ := ((frequently_cofinite_iff_infinite.2 p4).and_eventually
    (((locV hB hK hA hT hΦ).and (locV' hB hK hA hT hΦ')).and
      (((hV F E σ B _ _ _ _ G.M _ _ _ _ hT.base hT.geo.hV hT.geo.hW hT.geo.hM).and
        (hV F E σ B _ _ _ _ G.M' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM')).and
      (((im (mat h₀)).and (im (mat h₀⁻¹))).and (((im (incM F c.1)).and (im (incM F (c⁻¹).1))).and
        X.T.eventually_cofinite_notMem))))).exists
  obtain ⟨ι, S, a0, a1, a2, a3⟩ := h1 t
  obtain ⟨ι', S', b0, b1, b2, b3⟩ := h2 t
  obtain ⟨κ, hκ⟩ := v1 t ι a0
  obtain ⟨κ', hκ'⟩ := v2 t ι' b0
  obtain ⟨⟨sec, h⟩, us⟩ := section_statement F E σ hT.base.cm v t
  have hd := PositivityTheory.ThKF.detW (PositivityTheory.ThKG.pairV hT)
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := Fv F v)
  obtain ⟨c₀, c1, c2⟩ := exists_cond hϖ (ψ := χ.compAddMonoidHom (sA v sec)) (hχ.1.comp sA_cont) (psi_ne h hχ)
  choose b bz bd bU bT using fun i : ℕ => exists_torus h hm he hc hp (ϖ ^ i)
  have uα := p3 X.α _ hT.chars.unrα v hv t
  have uβ := p3 X.β _ hT.chars.unrβ v hv t
  obtain ⟨D, hD⟩ := hT.geo.even
  have hE := hT.geo.eBig
  obtain ⟨ε, rfl⟩ : ∃ ε, D = a' + ε := ⟨D - a', by omega⟩
  obtain rfl : a = a' + 2 * ε := by omega
  set q : ℕ := GlobalTheory.SplitWeil.resCard (Fv F v) with hq
  have q1 : 1 < q := Finite.one_lt_card
  have q0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have ap : ((apowH (((a' + 2 * ε + a' : ℕ) : ℂ) / 2) ϖ : ℂˣ) : ℂ) = ((q : ℂ) ^ (a' + ε))⁻¹ := by
    rw [show a' + 2 * ε + a' = 2 * (a' + ε) by omega]
    exact apow_unif hϖ _
  set r : ℂ := chrW X.α t ϖ / chrW X.β t ϖ * (q : ℂ) ^ ε with hr
  have r1 : ((((chrW (X.β / X.α) t * apowH (((a' + 2 * ε + a' : ℕ) : ℂ) / 2))⁻¹ : (Fv F v)ˣ →* ℂˣ) ϖ : ℂˣ) : ℂ) *
      (q : ℂ) ^ (((a' + 2 * ε : ℕ) : ℤ) - (a' + 2 * ε + a' : ℕ)) = r := by
    rw [show ((a' + 2 * ε : ℕ) : ℤ) - (a' + 2 * ε + a' : ℕ) = -(a' : ℤ) by push_cast; ring, MonoidHom.inv_apply, MonoidHom.mul_apply,
      Units.val_inv_eq_inv_val, Units.val_mul, ap, chrW_div, Units.val_div_eq_div_val, hr, zpow_neg, zpow_natCast, pow_add]
    field_simp
  have r2 : ((((chrW (X.α / X.β) t * apowH (((a' + 2 * ε + a' : ℕ) : ℂ) / 2))⁻¹ : (Fv F v)ˣ →* ℂˣ) ϖ : ℂˣ) : ℂ) *
      (q : ℂ) ^ (((a' : ℕ) : ℤ) - (a' + 2 * ε + a' : ℕ)) = r⁻¹ := by
    rw [show ((a' : ℕ) : ℤ) - (a' + 2 * ε + a' : ℕ) = -((a' + ε + ε : ℕ) : ℤ) by push_cast; ring, MonoidHom.inv_apply,
      MonoidHom.mul_apply, Units.val_inv_eq_inv_val, Units.val_mul, ap, chrW_div, Units.val_div_eq_div_val, hr, zpow_neg,
      zpow_natCast, pow_add _ (a' + ε)]
    field_simp
  have rn : (q : ℝ) < ‖r‖ := by
    rw [hr, norm_mul, norm_div, (us _ hT.chars.heckeα).1, (us _ hT.chars.heckeβ).1, div_one, one_mul, norm_pow, Complex.norm_natCast]
    exact_mod_cast lt_self_pow₀ q1 (by omega)
  have r0 : r ≠ 0 := norm_pos_iff.1 ((Nat.cast_nonneg q).trans_lt rn)
  have un : ∀ χ χ' : Chr F E, (∀ x : (Fv F v)ˣ, ValuativeRel.valuation _ (x : Fv F v) = 1 → chrW χ t x = 1) →
      (∀ x : (Fv F v)ˣ, ValuativeRel.valuation _ (x : Fv F v) = 1 → chrW χ' t x = 1) → ∀ z,
      ∀ x : (Fv F v)ˣ, ValuativeRel.valuation _ (x : Fv F v) = 1 →
        ((chrW (χ / χ') t * apowH z)⁻¹ : (Fv F v)ˣ →* ℂˣ) x = 1 := fun χ χ' k k' z x hx => by
    rw [MonoidHom.inv_apply, MonoidHom.mul_apply, chrW_div, k x hx, k' x hx,
      show apowH z x = 1 from Units.ext (apow_of_valuation_eq_one hx z)]
    simp
  refine ⟨{g | IntM (cp t g).1 ∧ IntM (cp t g⁻¹).1}, ?_, b, yy q r c₀, bz 0 (pow_zero _), bd,
    yy_tendsto (by exact_mod_cast q1) rn c₀, fun g hg => ?_⟩
  · have o : ∀ g₀ : UA σ G.W.J, IntM (cp t g₀).1 → ∀ᶠ g in 𝓝 g₀, IntM (cp t g).1 := fun g₀ hg =>
      eventually_all.2 fun i => eventually_all.2 fun j => (isOpen_int.preimage ((p1 v t).comp
        ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j))).mem_nhds (hg i j)
    exact (o h₀ (i1 t)).and ((continuous_inv.tendsto h₀).eventually (o h₀⁻¹ (i2 t)))
  · have ci := i3 t
    have ci' := i4 t
    rw [incM_map h] at ci ci'
    obtain ⟨x, hx⟩ := two hL h hd hT.geo.hW.skew hσ hu hΛ a2 a1 hκ (un _ _ uβ uα _) hϖ c1 c2 he
      (c := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) c) (fun a i => congrArg t (hc a i)) ci ci' bU
      (fun i => Units.val_pow_eq_pow_val ϖ i ▸ bT i) hg.1 hg.2
    obtain ⟨x', hx'⟩ := two hL h hd hT.geo.hW.skew hσ hu hΛ b2 b1 hκ' (un _ _ uα uβ _) hϖ c1 c2 he
      (c := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) c) (fun a i => congrArg t (hc a i)) ci ci' bU
      (fun i => Units.val_pow_eq_pow_val ϖ i ▸ bT i) hg.1 hg.2
    refine ⟨x - x' * r ^ c₀, fun i => ?_⟩
    rw [← a3, ← b3, wh_sub hΛ (a2.aut _ a1) (b2.aut _ b1), hx, hx', r1, r2, yy_inv _ r0]
    push_cast
    ring

end PartC

end PositivityTheory.ThKEnd.Cusp.Key

end
