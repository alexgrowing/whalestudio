import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

def ofLinear (g : D.La →ₗ[𝓞 F] D.La) (c k : ℕ) (hc : c.Coprime p) (hk : k.Coprime p)
    (hg : ∀ x y, D.EF (g x) (g y) = c * D.EF x y) (hon : ∀ x, ∃ y, g y = k • x) : IntSim D p where
  c := c
  k := k
  c_cop := hc
  k_cop := hk
  g _ := g
  compat n m _ a := ⟨0, by simp⟩
  sim n _ := ⟨1, isCoprime_one_left, fun a b => by rw [hg]; simp⟩
  onto n _ a := let ⟨y, hy⟩ := hon a; ⟨y, 0, by simp [hy]⟩

def scalar (D : Datum F) (m : ℕ) (hm : m.Coprime p) : IntSim D p :=
  ofLinear (D := D) (m • LinearMap.id) (m ^ 2) m (Nat.Coprime.pow_left 2 hm) hm
    (fun x y => by simp [LinearMap.map_smul_of_tower]; ring) (fun x => ⟨x, by simp⟩)

def one (D : Datum F) (p : ℕ) : IntSim D p :=
  ofLinear (D := D) (p := p) LinearMap.id 1 1 (Nat.coprime_one_left p) (Nat.coprime_one_left p) (by simp) (fun x => ⟨x, by simp⟩)

def comp (g₁ g₂ : IntSim D p) : IntSim D p where
  c := g₁.c * g₂.c
  k := g₁.k * g₂.k
  c_cop := Nat.Coprime.mul g₁.c_cop g₂.c_cop
  k_cop := Nat.Coprime.mul g₁.k_cop g₂.k_cop
  g n := g₁.g n ∘ₗ g₂.g n
  compat n m h a := by
    obtain ⟨b₂, hb₂⟩ := g₂.compat n m h a
    obtain ⟨b₁, hb₁⟩ := g₁.compat n m h (g₂.g (n * m) a)
    refine ⟨b₁ + g₁.g n b₂, ?_⟩
    have e : g₂.g n a = g₂.g (n * m) a - n • b₂ := by rw [← hb₂]; abel
    simp only [LinearMap.comp_apply]
    rw [e, map_sub, map_nsmul, smul_add, ← hb₁]
    abel
  sim n h := by
    obtain ⟨u₁, hu₁, h₁⟩ := g₁.sim n h
    obtain ⟨u₂, hu₂, h₂⟩ := g₂.sim n h
    refine ⟨u₁ * u₂, hu₁.mul_left hu₂, fun a b => ?_⟩
    have := dvd_add (h₁ (g₂.g n a) (g₂.g n b)) (Dvd.dvd.mul_left (h₂ a b) (g₁.c * u₁))
    simp only [LinearMap.comp_apply]
    obtain ⟨q, hq⟩ := this
    exact ⟨q, by push_cast; linear_combination hq⟩
  onto n h a := by
    obtain ⟨b₁, d₁, h₁⟩ := g₁.onto n h a
    obtain ⟨b₂, d₂, h₂⟩ := g₂.onto n h b₁
    refine ⟨b₂, g₂.k • d₁ + g₁.g n d₂, ?_⟩
    simp only [LinearMap.comp_apply]
    rw [h₂, map_add, map_nsmul, map_nsmul, h₁]
    module

theorem scalar_k (D : Datum F) (m : ℕ) (hm : m.Coprime p) : (scalar D m hm).k = m := rfl

theorem scalar_c (D : Datum F) (m : ℕ) (hm : m.Coprime p) : (scalar D m hm).c = m ^ 2 := rfl

end IntSim

variable {S : Scheme.{0}}

def HeckeRel {D : Datum F} {p N N' : ℕ} (g : IntSim D p) {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s)
    (o' : Obj D p N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ Etale ψ.left ∧
    (∀ x, o'.eta x = o.eta ((N' / (N * g.k)) • g.g N' x) ≫ ψ) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (t : Over.mk x ⟶ o.A),
      t ≫ ψ = 1 ↔ ∃ a, t = toUnit _ ≫ o.eta ((N' / g.k) • g.g N' a)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → n.Coprime p →
      ∀ (P Q : Over.mk x ⟶ o.A), P ^ n = 1 → Q ^ n = 1 → ∀ ζ : kˣ,
        Out.WeilIs o'.A o'.PP.L n (P ≫ ψ) (Q ≫ ψ) (unitOn ζ) →
          Out.WeilIs o.A o.PP.L ((g.k ^ 2 * n : ℕ) : ℤ) P Q (unitOn (ζ ^ g.c))

def IsHecke {D : Datum F} {p N N' : ℕ} (g : IntSim D p) (M' : IntModel D p N') (M : IntModel D p N)
    (π : M'.X ⟶ M.X) : Prop :=
  π ≫ M.s = M'.s ∧ ∃ (o : Obj D p N M'.s) (ψ : M'.univ.A ⟶ o.A), HeckeRel g M'.univ o ψ ∧ Nonempty (ObjMap o M.univ π)

end GlobalTheory.UPel
