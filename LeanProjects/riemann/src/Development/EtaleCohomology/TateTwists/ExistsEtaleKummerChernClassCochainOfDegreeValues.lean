import Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleKummerChernClassCochainOfLineBundle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev α 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev α 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev α 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def ExistsEtaleKummerChernClassCochain : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α

def EtaleKummerChernClassCochainIsCocycle : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α → δ 2 3 α = 0

def EvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def ExistsNaturalEtaleKummerChernClassDegreeOneValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def ExistsNaturalEtaleKummerChernClassDegreeTwoValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

noncomputable def vals {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 2 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 0, _, _, _, _ => 0
  | 1, s, h, U, x => (show (1 : ℤ) = s by omega) ▸ a1 U x
  | 2, s, h, U, x => (show (0 : ℤ) = s by omega) ▸ a2 U x
  | _ + 3, _, _, _, _ => 0

theorem vals_nat {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a1 U x) = a1 V (x.res g))
    (h2 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a2 U x) = a2 V (x.res g)) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (vals a1 a2 p s h U x) = vals a1 a2 p s h V (x.res g)
  | 0, _, _, V, U, g, x => by simp [vals]
  | 1, s, h, V, U, g, x => by obtain rfl : s = 1 := by omega
                              exact h1 V U g x
  | 2, s, h, V, U, g, x => by obtain rfl : s = 0 := by omega
                              exact h2 V U g x
  | _ + 3, _, _, V, U, g, x => by simp [vals]

theorem exists_etale_kummer_chern_class_cochain_of_degree_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) : ExistsEtaleKummerChernClassCochain := by
  intro q _ E L hi
  obtain ⟨a1, n1, e1⟩ := h1 q L hi
  obtain ⟨a2, n2, e2⟩ := h2 q L hi
  obtain ⟨α, hα⟩ := hmk (ZMod q) (vals a1 a2) (vals_nat a1 a2 n1 n2)
  refine ⟨α, ?_, ?_, ?_⟩
  · intro U x; rw [hα]; rfl
  · intro U x v hv; rw [hα]; exact e1 U x v hv
  · intro U x v w hv hw; rw [hα]; exact e2 U x v w hv hw

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) (hd : EtaleKummerChernClassCochainIsCocycle) :
    LateralTheory.EtaleFoundations.first_chern_class_exists := by
  intro q _ E L hi
  obtain ⟨α, hα⟩ := exists_etale_kummer_chern_class_cochain_of_degree_values hmk h1 h2 q L hi
  exact ⟨Cocycle.mk α 3 (by norm_num) (hd q L hi α hα), hα⟩
