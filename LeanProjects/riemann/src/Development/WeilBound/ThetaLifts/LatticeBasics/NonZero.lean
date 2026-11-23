import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

theorem res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' n)
    (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

theorem pairV (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    res_div h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem pairV' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem occ_fin {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {o : Rep σ Y W} {v : Pl F} {P : Type} [AddCommGroup P] [Module ℂ P]
    [Nontrivial P] {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P} (h1 : (SB _).map p = ⊤) (h2 : augAt o v ≤ LinearMap.ker p) :
    ∃ φ ∈ SB (Fin n × Fin d → Fv F v), φ ∉ augAt o v := by
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 (h1 ▸ Submodule.mem_top : x ∈ (SB _).map p)
  exact ⟨φ, hφ, fun h => hx (h2 h)⟩

theorem split_zero {W : Spc F E (a + a')} {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (X : Chars F E) :
    Split2 (σ := σ) (W := W) W₁ H' X 0 0 0 :=
  ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

theorem big_of (hB : NonZeroBot) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (q : ℕ) :
    ∀ (a' : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → G.q = q →
      ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  induction q with
  | zero => exact fun a' G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).1
  | succ q ih =>
    intro a' G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := h.geo.aBig; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B a b G X om om' h (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (c.ep.trans hp) (by have : G₁.q + 1 = G.q := c.eq; omega)
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') _ G₁.V G₁.W H' _ _ G₁.M c.eV c.hH' h₁.geo.hM
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B a b _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M.I om Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    have := hc X om om' om₁ om₁' h' h₁ Φ p2 0 0 (by
      show Split2 _ _ _ (G.M.I om Φ) 0 0
      rw [z]; exact split_zero _ _ _) g m hm 1
    have o : om (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om) Φ
    erw [o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem small_of (hB : NonZeroBot) (hT : TowerA) (hE : EvZero) (hC : CTSmallZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx)
    (hZ : SplitEx) (p : ℕ) :
    ∀ (a : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = p → G.q = 0 →
      ∃ Φ ∈ PolData B G.M', G.M'.I om' Φ ≠ 0 := by
  induction p with
  | zero => exact fun a G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).2
  | succ p ih =>
    intro a G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := h.geo.aBig; have := h.geo.lt; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B b a' G X om om' h hq (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (by have : G₁.p + 1 = G.p := c.ep; omega) c.q1
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') _ G₁.V' G₁.W H' _ _ G₁.M' c.eV c.hH' h₁.geo.hM'
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B b a' _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M'.I om' Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    obtain ⟨fa, s1, s2⟩ := hc X om om' om₁ om₁' h' h₁ Φ p2
    have s3 : Split2 G₁.W H' X (G.M'.I om' Φ) fa 0 := s1
    rw [z] at s3
    have i0 : (reG G V V' W).M.I om 0 = 0 := funext fun x => by simp [Model.I, theta, thetaSum]
    have fz : fa = 0 := congrArg Prod.fst (((hZ F E σ B _ _ (reG G V V' W) X om om' h' _ G₁.W H' _ _ c.hH').1 0 (zero_mem _)).unique
      (y₁ := (fa, 0)) (y₂ := (0, 0)) (by rw [i0]; exact s3) (by rw [i0]; exact split_zero _ _ _))
    have := s2 g m hm 1
    have o : om' (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om') Φ
    erw [fz, o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem nonZeroAn_of (hB : NonZeroBot) (hA : TowerA) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hC' : CTSmallZero)
    (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (hZ : SplitEx) (hO : ToSo) : NonZeroAn := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  refine ⟨fun hp => big_of hB hT hE hC hS hP hL _ a' G om om' h hp rfl, fun hq => ?_⟩
  obtain ⟨Φ, p1, n1⟩ := small_of hB hA hE hC' hS hP hL hZ _ a G om om' h rfl hq
  obtain ⟨Ψ, p2, e⟩ := hO F E σ B a a' G X om om' h hq Φ p1
  exact ⟨Ψ, p2, e ▸ n1⟩

end GlobalTheory.ThK.Dbl

end
