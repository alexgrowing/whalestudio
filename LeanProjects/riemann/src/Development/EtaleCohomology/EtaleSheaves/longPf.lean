import Development.EtaleCohomology.EtaleSheaves.CxDescPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.longPf
open LateralTheory.E.CxDescPf

def LES : Prop := ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x)

theorem four_inj {A B C D A' B' C' D' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D']
    (α : A →+ B) (β : B →+ C) (γ : C →+ D) (α' : A' →+ B') (β' : B' →+ C') (γ' : C' →+ D')
    (a : A →+ A') (b : B →+ B') (c : C →+ C') (d : D →+ D')
    (h2 : Function.Exact α β) (h2' : Function.Exact α' β') (h3 : Function.Exact β γ)
    (s1 : ∀ x, b (α x) = α' (a x)) (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x))
    (ha : Function.Surjective a) (hb : Function.Injective b) (hd : Function.Injective d) : Function.Injective c := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have : γ x = 0 := hd (by rw [s3, hx, map_zero, map_zero])
  obtain ⟨y, rfl⟩ := (h3 x).1 this
  have : β' (b y) = 0 := by rw [← s2]; exact hx
  obtain ⟨z', hz'⟩ := (h2' (b y)).1 this
  obtain ⟨z, rfl⟩ := ha z'
  have : α z = y := hb (by rw [s1, hz'])
  rw [← this]; exact h2.apply_apply_eq_zero z

theorem four_surj {B C D E B' C' D' E' : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D'] [AddCommGroup E']
    (β : B →+ C) (γ : C →+ D) (δ : D →+ E) (β' : B' →+ C') (γ' : C' →+ D') (δ' : D' →+ E')
    (b : B →+ B') (c : C →+ C') (d : D →+ D') (e : E →+ E')
    (h2' : Function.Exact β' γ') (h3 : Function.Exact γ δ) (h3' : Function.Exact γ' δ')
    (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x)) (s4 : ∀ x, e (δ x) = δ' (d x))
    (hb : Function.Surjective b) (hd : Function.Surjective d) (he : Function.Injective e) : Function.Surjective c := by
  intro x'
  obtain ⟨y, hy⟩ := hd (γ' x')
  have : δ y = 0 := he (by rw [s4, hy, map_zero, h3'.apply_apply_eq_zero])
  obtain ⟨w, rfl⟩ := (h3 y).1 this
  have : γ' (x' - c w) = 0 := by rw [map_sub, ← s3, hy, sub_self]
  obtain ⟨u', hu'⟩ := (h2' _).1 this
  obtain ⟨u, rfl⟩ := hb u'
  exact ⟨w + β u, by rw [map_add, s2, hu', add_sub_cancel]⟩

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre_mk]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_sq {R : Type} [CommRing R] {A B C D : Cx R} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (w : f ≫ g = f' ≫ g') (I : Cx R) (n : ℤ) (x) :
    cpull f I n (cpull g I n x) = cpull f' I n (cpull g' I n x) := by
  rw [← cpull_comp, ← cpull_comp, w]

def Ses : Prop := ∀ (R : Type) [CommRing R] (N : ℕ), ∃ (i : ∀ K : Cx R, tr K N ⟶ tr K (N + 1))
  (p : ∀ K : Cx R, tr K (N + 1) ⟶ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ))))
  (w : ∀ K, i K ≫ p K = 0), (∀ K, (ShortComplex.mk (i K) (p K) (w K)).ShortExact) ∧
  ∀ {K L : Cx R} (g : K ⟶ L), i K ≫ trm g (N + 1) = trm g N ≫ i L ∧
    p K ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) = trm g (N + 1) ≫ p L

theorem long_of (hLES : LES) (hSes : Ses) : LateralTheory.E.CxDescPf.long := by
  intro R _ I _ hI K L _ _ g m N h3 h1
  obtain ⟨d, hex, hnat⟩ := hLES R I hI
  obtain ⟨i, p, w, hse, hn⟩ := hSes R N
  let MainNotions := ShortComplex.mk (i K) (p K) (w K)
  let SL := ShortComplex.mk (i L) (p L) (w L)
  let φ : MainNotions ⟶ SL := ShortComplex.Hom.mk (trm g N) (trm g (N + 1))
    ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) (hn g).1.symm (hn g).2.symm
  have sf : ∀ j x, cpull φ.τ₁ I j (cpull SL.f I j x) = cpull MainNotions.f I j (cpull φ.τ₂ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₁₂ I j x
  have sg : ∀ j x, cpull φ.τ₂ I j (cpull SL.g I j x) = cpull MainNotions.g I j (cpull φ.τ₃ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₂₃ I j x
  have inj : ∀ n : ℤ, n + 1 ≤ m → Function.Injective (cpull φ.τ₂ I (n + 1)) := by
    intro n hn
    refine four_inj (d SL (hse L) n) (cpull SL.g I (n + 1)) (cpull SL.f I (n + 1))
      (d MainNotions (hse K) n) (cpull MainNotions.g I (n + 1)) (cpull MainNotions.f I (n + 1))
      (cpull φ.τ₁ I n) (cpull φ.τ₃ I (n + 1)) (cpull φ.τ₂ I (n + 1)) (cpull φ.τ₁ I (n + 1))
      (hex SL (hse L) n).2.2 (hex MainNotions (hse K) n).2.2 (hex SL (hse L) (n + 1)).1
      (fun x => hnat MainNotions SL (hse K) (hse L) φ n x) (sg (n + 1)) (sf (n + 1))
      (h1.1 n (by omega)).2 ?_ ?_
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h3.1 _ h).1
      · rw [h]; exact h3.2
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h1.1 _ h).1
      · rw [h]; exact h1.2
  have surj : ∀ j : ℤ, j < m → Function.Surjective (cpull φ.τ₂ I j) := by
    intro j hj
    refine four_surj (cpull SL.g I j) (cpull SL.f I j) (d SL (hse L) j)
      (cpull MainNotions.g I j) (cpull MainNotions.f I j) (d MainNotions (hse K) j)
      (cpull φ.τ₃ I j) (cpull φ.τ₂ I j) (cpull φ.τ₁ I j) (cpull φ.τ₃ I (j + 1))
      (hex MainNotions (hse K) j).1 (hex SL (hse L) j).2.1 (hex MainNotions (hse K) j).2.1
      (sg j) (sf j) (fun x => hnat MainNotions SL (hse K) (hse L) φ j x)
      (h3.1 j hj).2 (h1.1 j hj).2 ?_
    rcases lt_or_eq_of_le (show j + 1 ≤ m by omega) with h | h
    · exact (h3.1 _ h).1
    · rw [h]; exact h3.2
  have inj' : ∀ j : ℤ, j ≤ m → Function.Injective (cpull φ.τ₂ I j) := by
    intro j hj
    have := inj (j - 1) (by omega)
    rwa [sub_add_cancel] at this
  exact ⟨fun j hj => ⟨inj' j hj.le, surj j hj⟩, inj' m le_rfl⟩

end LateralTheory.E.longPf
