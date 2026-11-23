import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA

noncomputable section

namespace PositivityTheory.ThKG

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem alg_B {C₀ C₁ C₂ s l x y c : ℂ} (h : C₀ ≠ 0) (e : C₂ * s * l * x = c * y) :
    C₂ * C₁ / C₀ * s * l * (C₀ * x) = c * (C₁ * y) := by
  field_simp
  linear_combination C₁ * e

theorem alg_A {C₀ C₁ C₂ s l y c : ℂ} (h : C₀ ≠ 0) : C₁ * (c * (C₂ * s * l * y)) = C₂ * C₁ / C₀ * s * l * c * (C₀ * y) := by
  field_simp

theorem Below.mono {n m : ℕ} (h : Below n) (hm : m ≤ n) : Below m :=
  fun F E _ _ _ _ _ σ B a a' G X om om' R Rf t l => h F E σ B a a' G X om om' R Rf t (l.trans_le hm)

def KeyB (e₁ e₂ s : ℤˣ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b),
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      Below (G.p + G.q) →
      (∀ c₁, PolConst B G₁ X om₁ om₁' R₁ Rf₁ c₁ → ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb',
        Split2 G₁.W H' X (G.M.I om Φ) fa fb → Split2 G₁.W H' X (G.M'.I om' Φ') fa' fb' →
        ∀ h₁ m, IsLevi (W₁ := G₁.W) H' 1 h₁ m →
          (C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) *
            charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 : ℕ) : ℂ) + 1)) * fb m = c₁ * fb' m) ∧
      ∃ Φ ∈ PolData B G.M, ∀ fa fb, Split2 G₁.W H' X (G.M.I om Φ) fa fb →
        ∃ h₁ m, IsLevi (W₁ := G₁.W) H' 1 h₁ m ∧ fb m ≠ 0

theorem keyB_of (h0 : EvZero) (hc : EvCone) (hs : StabEx) (c0 : CTBigZero) (c1 : CTSmallCone) (hl : LocB') (hL : LeviEx) :
    ∃ e₁ e₂ s, KeyB e₁ e₂ s := by
  obtain ⟨e₁, e₂, s, hl⟩ := hl
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B a b G G₁ H H' cfg R R₁ => ?_⟩
  by_cases hw : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' Rf om₁ om₁' Rf₁ m m₁ => (hw ⟨X, om, om', om₁, om₁', m.triple, m₁.triple⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t, t₁⟩ := hw
  obtain ⟨⟨e, he⟩, hon⟩ := h0 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) _ G₁.V G₁.W H' _ _ G₁.M cfg.eV cfg.hH' t₁.geo.hM
  obtain ⟨-, e', he'⟩ := hc F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ _ G₁.V' G₁.W H H' _ _ _ _ G₁.M' cfg.hH cfg.hH' t₁.geo.hM'
  obtain ⟨K, μK, μ, hK, -, hμK, hμ⟩ := hs F E σ B _ G.V' _ _ t.base t.geo.hV'
  obtain ⟨C₀, hC₀, k0⟩ := c0 F E σ B a b G G₁ H H' cfg e he
  obtain ⟨C₁, hC₁, k1⟩ := c1 F E σ B a b G G₁ H H' cfg e' he' K μK μ hK hμK hμ
  obtain ⟨C₂, hC₂, k2⟩ := hl F E σ B a b G G₁ H H' cfg R R₁ e e' he he' K μK μ hK hμK hμ
  refine ⟨C₂ * C₁ / C₀, div_ne_zero (mul_ne_zero hC₂ hC₁) hC₀, fun X om om' Rf om₁ om₁' Rf₁ m m₁ hB => ⟨?_, ?_⟩⟩
  · intro c₁ hc₁ Φ Φ' hΦ' hm fa fb fa' fb' sp sp' h₁ l hlv
    have a0 := k0 X om om' om₁ om₁' m.triple m₁.triple Φ (polMatch_mem hm).1 fa fb sp h₁ l hlv 1
    have a1 := k1 X om om' om₁ om₁' m.triple m₁.triple Φ' ⟨(polMatch_mem hm).2, hΦ'⟩ fa' fb' sp' h₁ l hlv 1
    obtain ⟨so, pm⟩ := k2 X om om' Rf om₁ om₁' Rf₁ m m₁ hB Φ Φ' hΦ' hm
    have a2 := hc₁ _ _ so pm h₁
    rw [I_smul] at a2
    rw [mul_one, Prod.mk_one_one, map_one, Module.End.one_apply] at a0 a1
    rw [a0, a1]
    exact alg_B hC₀ a2
  · have hlt : G₁.p + G₁.q < G.p + G.q := by have := cfg.ep; have := cfg.eq; omega
    obtain ⟨-, ⟨Φ₁, h1, hne⟩, -⟩ := hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt
    rw [← hon e he] at h1
    obtain ⟨Φ, hΦ, rfl⟩ := h1
    refine ⟨Φ, hΦ, fun fa fb sp => ?_⟩
    obtain ⟨h₁, hh⟩ := Function.ne_iff.1 hne
    obtain ⟨l, hlv⟩ := hL F E σ B _ _ G.W G₁.W H' _ _ _ _ t.base t.geo.hW cfg.hH' h₁
    have a0 := k0 X om om' om₁ om₁' m.triple m₁.triple Φ hΦ fa fb sp h₁ l hlv 1
    rw [mul_one, Prod.mk_one_one, map_one, Module.End.one_apply] at a0
    exact ⟨h₁, l, hlv, a0 ▸ mul_ne_zero hC₀ hh⟩

def RelA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' d₁ : ℕ} (G : Geo σ a a') (W₁ : Spc F E d₁)
    (H' : Plane E (a + a') d₁) (X : Chars F E) (f f' fa' : UA σ G.W.J → ℂ) (k : ℂ) : Prop :=
  Split2 W₁ H' X f' fa' 0 ∧ ∀ fa fb, Split2 W₁ H' X f fa fb → ∀ h₁ m, IsLevi (W₁ := W₁) H' 1 h₁ m → fa m = k * fa' m

def KeyA (e₁ e₂ s : ℤˣ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a'),
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      Below (G.p + G.q) → ∀ c₁, PolConst B G₁ X om₁ om₁' R₁ Rf₁ c₁ → ∀ k,
        k = C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) *
          charL X.ν (X.S₀ : Set (Pl F)) (((b + 2 - a') / 2 : ℕ) : ℂ) * c₁ →
        (∀ Φ Φ', PolMatch B G X R Rf Φ Φ' → ∃ fa', RelA G G₁.W H' X (G.M.I om Φ) (G.M'.I om' Φ') fa' k) ∧
        ∃ Φ Φ' fa', PolMatch B G X R Rf Φ Φ' ∧ RelA G G₁.W H' X (G.M.I om Φ) (G.M'.I om' Φ') fa' k ∧
          ∃ h₁ m, IsLevi (W₁ := G₁.W) H' 1 h₁ m ∧ fa' m ≠ 0

theorem keyA_of (h0 : EvZero) (hc : EvCone) (hs : StabEx) (c0 : CTSmallZero) (c1 : CTBigCone) (hl : LocA') (hL : LeviEx)
    (hA : AnAll) (hM : MatchEx) : ∃ e₁ e₂ s, KeyA e₁ e₂ s := by
  obtain ⟨e₁, e₂, s, hl⟩ := hl
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B b a' G G₁ H H' cfg R R₁ => ?_⟩
  by_cases hw : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' Rf om₁ om₁' Rf₁ m m₁ => (hw ⟨X, om, om', om₁, om₁', m.triple, m₁.triple⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t, t₁⟩ := hw
  obtain ⟨⟨e', he'⟩, hon⟩ := h0 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' t) _ G₁.V' G₁.W H' _ _ G₁.M' cfg.eV cfg.hH' t₁.geo.hM'
  obtain ⟨⟨e, he⟩, -⟩ := hc F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) _ _ G₁.V G₁.W H H' _ _ _ _ G₁.M cfg.hH cfg.hH' t₁.geo.hM
  obtain ⟨K, μK, μ, hK, -, hμK, hμ⟩ := hs F E σ B _ G.V _ _ t.base t.geo.hV
  obtain ⟨C₀, hC₀, k0⟩ := c0 F E σ B b a' G G₁ H H' cfg e' he'
  obtain ⟨C₁, hC₁, k1⟩ := c1 F E σ B b a' G G₁ H H' cfg e he K μK μ hK hμK hμ
  obtain ⟨C₂, hC₂, k2⟩ := hl F E σ B b a' G G₁ H H' cfg R R₁ e e' he he' K μK μ hK hμK hμ
  refine ⟨C₂ * C₁ / C₀, div_ne_zero (mul_ne_zero hC₂ hC₁) hC₀, fun X om om' Rf om₁ om₁' Rf₁ m m₁ hB c₁ hc₁ k hk => ?_⟩
  have main : ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' → ∃ fa', RelA G G₁.W H' X (G.M.I om Φ) (G.M'.I om' Φ') fa' k ∧
      ∀ h₁ l, IsLevi (W₁ := G₁.W) H' 1 h₁ l → fa' l = C₀ * G₁.M'.I om₁' (e' Φ') h₁ := by
    intro Φ Φ' hm
    obtain ⟨fa', sp', a0⟩ := k0 X om om' om₁ om₁' m.triple m₁.triple Φ' (polMatch_mem hm).2
    have a0' : ∀ h₁ l, IsLevi (W₁ := G₁.W) H' 1 h₁ l → fa' l = C₀ * G₁.M'.I om₁' (e' Φ') h₁ := fun h₁ l hlv => by
      have := a0 h₁ l hlv 1
      rwa [mul_one, Prod.mk_one_one, map_one, Module.End.one_apply] at this
    refine ⟨fa', ⟨sp', fun fa fb sp h₁ l hlv => ?_⟩, a0'⟩
    have a1 := k1 X om om' om₁ om₁' m.triple m₁.triple Φ (polMatch_mem hm).1 fa fb sp h₁ l hlv 1
    rw [mul_one, Prod.mk_one_one, map_one, Module.End.one_apply] at a1
    have a2 := hA F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ cfg.q1 c₁ hc₁ _ _ (k2 X om om' Rf om₁ om₁' Rf₁ m m₁ hB Φ Φ' hm) h₁
    rw [I_smul] at a2
    rw [a1, a0' h₁ l hlv, a2, hk]
    exact alg_A hC₀
  refine ⟨fun Φ Φ' hm => (main Φ Φ' hm).imp fun _ h => h.1, ?_⟩
  have hlt : G₁.p + G₁.q < G.p + G.q := by have := cfg.ep; have := cfg.q0; have := cfg.q1; omega
  obtain ⟨-, -, Φ₁, ⟨h1, -⟩, hne⟩ := hB F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ hlt
  rw [SetLike.mem_coe, ← hon e' he'] at h1
  obtain ⟨Φ', hΦ', rfl⟩ := h1
  obtain ⟨Φ, hm⟩ := (hM F E σ B _ _ G X om om' R Rf m).2.1 Φ' hΦ'
  obtain ⟨fa', rel, a0⟩ := main Φ Φ' hm
  obtain ⟨h₁, hh⟩ := Function.ne_iff.1 hne
  obtain ⟨l, hlv⟩ := hL F E σ B _ _ G.W G₁.W H' _ _ _ _ t.base t.geo.hW cfg.hH' h₁
  exact ⟨Φ, Φ', fa', hm, rel, h₁, l, hlv, a0 h₁ l hlv ▸ mul_ne_zero hC₀ hh⟩

end PositivityTheory.ThKG

end
