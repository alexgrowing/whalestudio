import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CategoryTheory

namespace GlobalTheory

theorem exists_compatible_family_mod_of_levels :
    ∀ (L : Type) [AddCommGroup L] [Module.Finite ℤ L] (P : ℕ → (L →+ L) → Prop), (∀ (n : ℕ) (g g' : L →+ L), 0 < n → P n g → (∀ a, ∃ b, g' a - g a = n • b) → P n g') → (∀ (n m : ℕ) (g : L →+ L), 0 < n → 0 < m → P (n * m) g → P n g) → (∀ n : ℕ, 0 < n → ∃ g, P n g) → ∃ f : ℕ → L →+ L, (∀ n : ℕ, 0 < n → P n (f n)) ∧ ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ b, f (n * m) a - f n a = n • b := by
  intro L _ _ P _ h2 h3
  have hfg : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨s, hs⟩ := hfg.out
  let S : ℕ → AddSubgroup L := fun n => (nsmulAddMonoidHom n : L →+ L).range
  have memS : ∀ n x, x ∈ S n ↔ ∃ y, n • y = x := fun n x => Iff.rfl
  have finS : ∀ n, 0 < n → Finite (L ⧸ S n) := fun n hn =>
    AddCommGroup.finite_of_fg_torsion _ fun q => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨x, rfl⟩
  have hle : ∀ k j : ℕ, k ≤ j → S j.factorial ≤ (S k.factorial).comap (AddMonoidHom.id L) := by
    intro k j hkj x hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hkj
    refine ⟨c • y, ?_⟩
    change k.factorial • c • y = j.factorial • y
    rw [← mul_smul, ← hc]
  let key : ∀ n, (L →+ L) → s → L ⧸ S n := fun n g i => QuotientAddGroup.mk (g i)
  let Cls : ℕ → Type := fun k => {q : s → L ⧸ S k.factorial // ∃ g, P k.factorial g ∧ key _ g = q}
  let res : ∀ k j : ℕ, k ≤ j → Cls j → Cls k := fun k j h q =>
    ⟨fun i => QuotientAddGroup.map _ _ (AddMonoidHom.id L) (hle k j h) (q.1 i), by
      obtain ⟨g, hg, hq⟩ := q.2
      obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial h
      refine ⟨g, h2 _ c g (Nat.factorial_pos k) ?_ (hc ▸ hg), ?_⟩
      · rcases Nat.eq_zero_or_pos c with h0 | h0
        · exfalso; have := Nat.factorial_pos j; rw [hc, h0, mul_zero] at this; exact lt_irrefl _ this
        · exact h0
      · funext i; rw [← hq]; rfl⟩
  have hres_id : ∀ k (h : k ≤ k) (q : Cls k), res k k h q = q := by
    intro k h q; apply Subtype.ext; funext i
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (q.1 i)
    change QuotientAddGroup.map _ _ (AddMonoidHom.id L) _ (q.1 i) = q.1 i
    rw [← hx]; rfl
  have hres_comp : ∀ k j l (h : k ≤ l) (h1 : k ≤ j) (h2 : j ≤ l) (q : Cls l),
      res k l h q = res k j h1 (res j l h2 q) := by
    intro k j l h h1 h2 q; apply Subtype.ext; funext i
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (q.1 i)
    change QuotientAddGroup.map _ _ (AddMonoidHom.id L) _ (q.1 i) =
      QuotientAddGroup.map _ _ (AddMonoidHom.id L) _ (QuotientAddGroup.map _ _ (AddMonoidHom.id L) _ (q.1 i))
    rw [← hx]; rfl
  let F : ℕᵒᵖ ⥤ Type := {
    obj := fun k => Cls k.unop
    map := fun {k j} f => TypeCat.ofHom (res j.unop k.unop (leOfHom f.unop))
    map_id := by
      intro k; ext q i
      exact congrArg (fun r : Cls _ => r.1 i) (hres_id _ le_rfl q)
    map_comp := by
      intro k j l f f'; ext q i
      exact congrArg (fun r : Cls _ => r.1 i)
        (hres_comp _ _ _ ((leOfHom f'.unop).trans (leOfHom f.unop)) (leOfHom f'.unop) (leOfHom f.unop) q) }
  haveI : ∀ k : ℕᵒᵖ, Finite (F.obj k) := fun k => by
    haveI := finS _ (Nat.factorial_pos k.unop)
    change Finite (Cls k.unop)
    exact Subtype.finite
  haveI : ∀ k : ℕᵒᵖ, Nonempty (F.obj k) := fun k => by
    obtain ⟨g, hg⟩ := h3 _ (Nat.factorial_pos k.unop)
    exact ⟨⟨key _ g, g, hg, rfl⟩⟩
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system F
  have hsp : ∀ k, ∃ g, P k.factorial g ∧ key _ g = (x (Opposite.op k)).1 := fun k => (x (Opposite.op k)).2
  choose g hgP hgk using hsp
  have compat : ∀ k j : ℕ, k ≤ j → ∀ a, g j a - g k a ∈ S k.factorial := by
    intro k j hkj
    have e : res k j hkj (x (Opposite.op j)) = x (Opposite.op k) := hx (homOfLE hkj).op
    have hkey : ∀ i : s, (QuotientAddGroup.mk (g j i) : L ⧸ S k.factorial) = QuotientAddGroup.mk (g k i) := by
      intro i
      have e1 : QuotientAddGroup.map _ _ (AddMonoidHom.id L) (hle k j hkj) ((x (Opposite.op j)).1 i) =
          (x (Opposite.op k)).1 i := congrArg (fun q : Cls k => q.1 i) e
      rw [← hgk k, ← hgk j] at e1
      exact e1
    have hcl : AddSubgroup.closure (s : Set L) ≤ (S k.factorial).comap (g j - g k) := by
      rw [AddSubgroup.closure_le]
      intro a ha
      have := hkey ⟨a, ha⟩
      rw [QuotientAddGroup.eq] at this
      change (g j - g k) a ∈ S k.factorial
      have e2 : (g j - g k) a = -(-(g j a) + g k a) := by simp [sub_eq_add_neg, add_comm]
      rw [e2]; exact neg_mem this
    intro a
    have ha : a ∈ AddSubgroup.closure (s : Set L) := hs ▸ AddSubgroup.mem_top a
    exact hcl ha
  refine ⟨g, fun n hn => ?_, fun n m hn hm a => ?_⟩
  · refine h2 n (n - 1).factorial (g n) hn (Nat.factorial_pos _) ?_
    rw [Nat.mul_factorial_pred hn.ne']; exact hgP n
  · obtain ⟨y, hy⟩ := compat n (n * m) (Nat.le_mul_of_pos_right n hm) a
    refine ⟨(n - 1).factorial • y, ?_⟩
    rw [← hy]
    change n.factorial • y = n • (n - 1).factorial • y
    rw [← mul_smul, Nat.mul_factorial_pred hn.ne']

end GlobalTheory
