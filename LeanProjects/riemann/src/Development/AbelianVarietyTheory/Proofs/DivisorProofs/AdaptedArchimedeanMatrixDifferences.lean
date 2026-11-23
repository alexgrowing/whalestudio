import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchLinearCombination

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.OneParam GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.RealK

noncomputable section

namespace GlobalTheory.ThK.GenAssemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Good

variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def goodSub (M : Model σ Y W) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y W) : Submodule ℂ (Fn F n d) where
  carrier := {Φ | (∀ x, om x Φ ∈ schA F (Fin n × Fin d)) ∧ M.Conv om Φ}
  add_mem' := fun {Φ Ψ} hΦ hΨ => ⟨fun x => by rw [map_add]; exact add_mem (hΦ.1 x) (hΨ.1 x), fun h => by
      have e : (fun g => theta om (Φ + Ψ) g h) = fun g => theta om Φ g h + theta om Ψ g h := funext fun g => by
        simp only [theta, map_add]; exact thetaSum_add F (hΦ.1 _) (hΨ.1 _)
      rw [e]; exact (hΦ.2 h).add (hΨ.2 h)⟩
  zero_mem' := ⟨fun x => by rw [map_zero]; exact zero_mem _, fun h => by
      have e : (fun g => theta om (0 : Fn F n d) g h) = fun _ => 0 := funext fun g => by
        simp [theta, thetaSum]
      rw [e]; exact MeasureTheory.integrableOn_zero⟩
  smul_mem' := fun c Φ hΦ => ⟨fun x => by rw [map_smul]; exact Submodule.smul_mem _ c (hΦ.1 x), fun h => by
      have e : (fun g => theta om (c • Φ) g h) = fun g => c * theta om Φ g h := funext fun g => by
        simp only [theta, map_smul]; exact thetaSum_smul F c _
      rw [e]; exact (hΦ.2 h).const_mul c⟩

theorem I_smul (M : Model σ Y W) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y W) (c : ℂ) (Φ : Fn F n d) :
    M.I om (c • Φ) = c • M.I om Φ := funext fun h => by
  show (∫ g in M.dom, theta om (c • Φ) g h ∂M.μ) = c * ∫ g in M.dom, theta om Φ g h ∂M.μ
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (c • Φ)) = c * thetaSum F (om (g, h) Φ)
  rw [map_smul, thetaSum_smul]

theorem I_add (M : Model σ Y W) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y W) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ goodSub M om)
    (hΨ : Ψ ∈ goodSub M om) : M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := funext fun h => by
  show (∫ g in M.dom, theta om (Φ + Ψ) g h ∂M.μ) =
    (∫ g in M.dom, theta om Φ g h ∂M.μ) + ∫ g in M.dom, theta om Ψ g h ∂M.μ
  rw [← MeasureTheory.integral_add (hΦ.2 h) (hΨ.2 h)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (Φ + Ψ)) = thetaSum F (om (g, h) Φ) + thetaSum F (om (g, h) Ψ)
  rw [map_add, thetaSum_add F (hΦ.1 _) (hΨ.1 _)]

theorem I_sub (M : Model σ Y W) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y W) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ goodSub M om)
    (hΨ : Ψ ∈ goodSub M om) : M.I om (Φ - Ψ) = M.I om Φ - M.I om Ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, I_add M om hΦ (Submodule.smul_mem _ _ hΨ), I_smul, neg_one_smul,
    ← sub_eq_add_neg]

end Good

section Pure

variable {κ : Type} [Fintype κ]

theorem pure_add (f g : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul (c : ℂ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_sub (f g : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

end Pure

end GlobalTheory.ThK.GenAssemble

namespace GlobalTheory.ThK.GenAssemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Match

variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def Dat (M : Model σ Y W) : Type :=
  {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ // (∀ v, φ v ∈ SB _) ∧ ∀ᶠ v in Filter.cofinite, φ v = M.vac v}

open Classical in

def Dat.T {M : Model σ Y W} (X : Chars F E) (φ : Dat M) : Finset (Pl F) :=
  X.T ∪ (Filter.eventually_cofinite.1 φ.2.2).toFinset

open Classical in
theorem Dat.chars_T_subset_dat_T {M : Model σ Y W} (X : Chars F E) (φ : Dat M) : X.T ⊆ φ.T X := Finset.subset_union_left

open Classical in
theorem Dat.eq_vac {M : Model σ Y W} (X : Chars F E) (φ : Dat M) : ∀ v ∉ φ.T X, φ.1 v = M.vac v := fun v hv => by
  by_contra h
  exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))

end Match

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem polMatch_zero : PolMatch B G X R Rf 0 0 :=
  ⟨X.T, le_rfl, 0, 0, Fin.elim0, fun i => i.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    by simp, by simp, by simp⟩

theorem polMatch_pure_zero {f : SInf F (Fin a × Fin (a + a'))} (hf : f ∈ G.M.Pol B.ψ B.emb) (hp : R.p f = 0)
    (φ : Dat G.M) : PolMatch B G X R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ.1) 0 :=
  ⟨φ.T X, φ.chars_T_subset_dat_T X, 1, 0, fun _ => f, fun _ => φ.1, Fin.elim0, fun i => i.elim0,
    fun _ => ⟨hf, φ.2.1, φ.eq_vac X⟩, fun i => i.elim0, by simp, by simp, by simp [hp]⟩

theorem polMatch_zero_sub (hM : IsMatched B G X om om' R Rf) {Φ Ψ : Fn F a (a + a')} {Φ' Ψ' : Fn F a' (a + a')}
    (hΦ : PolMatch B G X R Rf Φ Φ') (hΨ : PolMatch B G X R Rf Ψ Ψ') (e : Φ = Ψ) :
    PolMatch B G X R Rf 0 (Φ' - Ψ') := by
  have := GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hM _ _ _ _ (-1) hΨ hΦ
  have e1 : (-1 : ℂ) • Ψ + Φ = 0 := by rw [e]; module
  have e2 : (-1 : ℂ) • Ψ' + Φ' = Φ' - Ψ' := by module
  rwa [e1, e2] at this

variable (B G X om om' R Rf) in

structure Hyp : Prop where
  m : IsMatched B G X om om' R Rf
  f1 : ∀ Φ, PolMatch B G X R Rf Φ 0 → G.M.I om Φ = 0
  f2 : ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf 0 Φ' → G.M'.I om' Φ' = 0
  part : ∀ Φ ∈ PolData B G.M, ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ'
  gP : ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ φ : Dat G.M, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ.1 ∈ goodSub G.M om
  gV' : ∀ Φ Φ', Φ' ∈ G.M'.So B.ψ B.τ₁ → PolMatch B G X R Rf Φ Φ' → Φ' ∈ goodSub G.M' om'

variable (B G X om om' R Rf) in

def Val (c : ℂ) (φ : Dat G.M) (π : R.Pi) (g : UA σ G.W.J → ℂ) : Prop :=
  ∃ f ∈ G.M.Pol B.ψ B.emb, R.p f = π ∧ ∃ Φ' ∈ G.M'.So B.ψ B.τ₁,
    PolMatch B G X R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ.1) Φ' ∧
      g = G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ.1) - c • G.M'.I om' Φ'

section Val

variable (hy : Hyp B G X om om' R Rf) (c : ℂ) (φ : Dat G.M)
include hy

theorem pure_mem_polData {f : SInf F (Fin a × Fin (a + a'))} (hf : f ∈ G.M.Pol B.ψ B.emb) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ.1 ∈ PolData B G.M :=
  Submodule.subset_span ⟨f, hf, φ.1, φ.2.1, φ.2.2, rfl⟩

theorem val_exists (π : R.Pi) : ∃ g, Val B G X om om' R Rf c φ π g := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 (hy.m.real.quot.onto ▸ Submodule.mem_top : π ∈ (G.M.Pol B.ψ B.emb).map R.p)
  obtain ⟨Φ', hΦ', hm⟩ := hy.part _ (pure_mem_polData hy φ hf)
  exact ⟨_, f, hf, rfl, Φ', hΦ', hm, rfl⟩

theorem val_unique {π : R.Pi} {g₁ g₂ : UA σ G.W.J → ℂ} (h₁ : Val B G X om om' R Rf c φ π g₁)
    (h₂ : Val B G X om om' R Rf c φ π g₂) : g₁ = g₂ := by
  obtain ⟨f₁, hf₁, e₁, Φ₁, hΦ₁, m₁, rfl⟩ := h₁
  obtain ⟨f₂, hf₂, e₂, Φ₂, hΦ₂, m₂, rfl⟩ := h₂
  have h0 : PolMatch B G X R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ - f₂) φ.1) 0 :=
    polMatch_pure_zero (sub_mem hf₁ hf₂) (by rw [map_sub, e₁, e₂, sub_self]) φ
  have hI : G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ.1) = G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₂ φ.1) := by
    have := hy.f1 _ h0
    rw [pure_sub, I_sub _ _ (hy.gP _ hf₁ φ) (hy.gP _ hf₂ φ), sub_eq_zero] at this
    exact this
  have hm : PolMatch B G X R Rf 0 (Φ₁ - Φ₂) := by
    have h3 := GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hy.m _ _ _ _ 1 m₂ h0
    have e3 : (1 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₂ φ.1 + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ - f₂) φ.1 =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ.1 := by rw [pure_sub]; module
    rw [e3, one_smul, add_zero] at h3
    exact polMatch_zero_sub hy.m m₁ h3 rfl
  have hI' : G.M'.I om' Φ₁ = G.M'.I om' Φ₂ := by
    have := hy.f2 _ (sub_mem hΦ₁ hΦ₂) hm
    rwa [I_sub _ _ (hy.gV' _ _ hΦ₁ m₁) (hy.gV' _ _ hΦ₂ m₂), sub_eq_zero] at this
  rw [hI, hI']

theorem val_add {π₁ π₂ : R.Pi} {g₁ g₂ : UA σ G.W.J → ℂ} (h₁ : Val B G X om om' R Rf c φ π₁ g₁)
    (h₂ : Val B G X om om' R Rf c φ π₂ g₂) : Val B G X om om' R Rf c φ (π₁ + π₂) (g₁ + g₂) := by
  obtain ⟨f₁, hf₁, rfl, Φ₁, hΦ₁, m₁, rfl⟩ := h₁
  obtain ⟨f₂, hf₂, rfl, Φ₂, hΦ₂, m₂, rfl⟩ := h₂
  have h3 := GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hy.m _ _ _ _ 1 m₁ m₂
  rw [one_smul, one_smul, ← pure_add] at h3
  refine ⟨f₁ + f₂, add_mem hf₁ hf₂, map_add _ _ _, Φ₁ + Φ₂, add_mem hΦ₁ hΦ₂, h3, ?_⟩
  rw [pure_add, I_add _ _ (hy.gP _ hf₁ φ) (hy.gP _ hf₂ φ), I_add _ _ (hy.gV' _ _ hΦ₁ m₁) (hy.gV' _ _ hΦ₂ m₂)]
  module

theorem val_smul (s : ℂ) {π : R.Pi} {g : UA σ G.W.J → ℂ} (h : Val B G X om om' R Rf c φ π g) :
    Val B G X om om' R Rf c φ (s • π) (s • g) := by
  obtain ⟨f, hf, rfl, Φ', hΦ', m, rfl⟩ := h
  have h3 := GlobalTheory.PolMatchLin.polMatch_smul_add F E σ B a a' G X om om' R Rf hy.m _ _ _ _ s m polMatch_zero
  rw [add_zero, add_zero, ← pure_smul] at h3
  refine ⟨s • f, Submodule.smul_mem _ s hf, map_smul _ _ _, s • Φ', Submodule.smul_mem _ s hΦ', h3, ?_⟩
  rw [pure_smul, I_smul, I_smul]
  module

def psi : R.Pi →ₗ[ℂ] (UA σ G.W.J → ℂ) where
  toFun π := (val_exists hy c φ π).choose
  map_add' π₁ π₂ := val_unique hy c φ (val_exists hy c φ _).choose_spec
    (val_add hy c φ (val_exists hy c φ π₁).choose_spec (val_exists hy c φ π₂).choose_spec)
  map_smul' s π := val_unique hy c φ (val_exists hy c φ _).choose_spec
    (val_smul hy c φ s (val_exists hy c φ π).choose_spec)

end Val

end GlobalTheory.ThK.GenAssemble

namespace GlobalTheory.ThK.GenAssemble

section FinsuppMod

variable {P Q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

variable (act : Mat P Q →ₗ[ℂ] Module.End ℂ V) (D : Type) in

def actF : Mat P Q →ₗ[ℂ] Module.End ℂ (D →₀ V) where
  toFun Z := Finsupp.mapRange.linearMap (act Z)
  map_add' Z₁ Z₂ := by ext d x e; simp
  map_smul' s Z := by ext d x e; simp

variable {act : Mat P Q →ₗ[ℂ] Module.End ℂ V} {D : Type}

end FinsuppMod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}

section Der

variable (hy : Hyp B G X om om' R Rf) (c : ℂ)
include hy

def phi : (Dat G.M →₀ R.Pi) →ₗ[ℂ] (UA σ G.W.J → ℂ) := Finsupp.lsum ℂ fun φ => psi hy c φ

end Der

end GlobalTheory.ThK.GenAssemble

namespace GlobalTheory.ThK.GenAssemble

end GlobalTheory.ThK.GenAssemble
