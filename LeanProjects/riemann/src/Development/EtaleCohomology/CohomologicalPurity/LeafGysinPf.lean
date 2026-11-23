import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

def LeafPur : Prop := Hyp → ∀ d, ∃ pur : ∀ (q : ℕ) (P : SP d) (n i : ℤ),
    Ht q (sch.obj P.Z) n i →+ Hs q (opn P.U) (n + 2 * d) (i + d),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  (∀ n i : ℤ, Function.Bijective (pur q P n i)) ∧
  (∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (pur q P n i a) = pur q P' n i (pull _ (sch.map φ.g) _ _ a)) ∧
  (∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    (Hs.fgt q (opn P.U) (n + m + 2 * d) (i + j + d) (pur q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)) :
      Ht q (sch.obj P.X) (n + m + 2 * d) (i + j + d)) =
      (cup q a (Hs.fgt q (opn P.U) (m + 2 * d) (j + d) (pur q P m j b) : Ht q (sch.obj P.X) (m + 2 * d) (j + d))).cast
        (by ring) (by ring)) ∧
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    (pur r P n i (red q r _ _ _ a)).1 = red q r _ _ _ (pur q P n i a).1

namespace GysinPf

theorem mono_opn {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  haveI : ∀ k, Mono ((sch.map U.ι).app k) := fun _ => by
    change Mono (yoneda.map U.ι); infer_instance
  exact NatTrans.mono_of_mono_app _

def castHs {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) : Hs q P a i →+ Hs q P b i := by
  subst h; exact AddMonoidHom.id _

theorem castHs_bij {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) :
    Function.Bijective (castHs (q := q) (P := P) i h) := by
  subst h; exact Function.bijective_id

theorem castHs_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {a b : ℤ} (i : ℤ) (h : a = b) (x : Hs q P a i) :
    Hs.pull q φ b i (castHs i h x) = castHs i h (Hs.pull q φ a i x) := by
  subst h; rfl

theorem castHs_val {Q q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) (x : Hs Q P a i) (y : Hs q P a i)
    (hxy : y.1 = red Q q _ a i x.1) : (castHs i h y).1 = red Q q _ b i (castHs i h x).1 := by
  subst h; exact hxy

theorem fgt_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right _ _ (Hs.fgt q P n i x) := by
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp,
    show dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P from pushout.inl_desc _ _ _]

theorem fgt_red {Q q : ℕ} {P : Arrow Spc} (n i : ℤ) (x : Hs Q P n i) (y : Hs q P n i)
    (h : y.1 = red Q q _ n i x.1) : Hs.fgt q P n i y = red Q q _ n i (Hs.fgt Q P n i x) := by
  change pull _ (dbl.inl P) _ n y.1 = red Q q _ n i (pull _ (dbl.inl P) _ n x.1)
  rw [h, pull_red]

theorem exact_cast {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) {M : Type*} [AddCommGroup M]
    (f : M →+ Hs q P a i) (hf : Function.Exact f (Hs.fgt q P a i)) :
    Function.Exact ((castHs i h).comp f) (Hs.fgt q P b i) := by
  subst h; exact hf

end GysinPf

open GysinPf in

theorem LeafGysin_of (hBd : LeafBd) (hPur : LeafPur) : LeafGysin := by
  intro hH d
  obtain ⟨δ, hex, hnatδ, hredδ⟩ := hBd
  obtain ⟨pur, hp⟩ := hPur hH d
  classical
  let gys : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.Z) n i →+ Ht q (sch.obj P.X) (n + 2 * d) (i + d) :=
    fun q P n i => (Hs.fgt q (opn P.U) (n + 2 * d) (i + d)).comp (pur q P n i)
  let rs : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.U) (n + 2 * d - 1) (i + d) →+ Ht q (sch.obj P.Z) n i :=
    fun q P n i => if h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) then
      (AddEquiv.ofBijective _ ((@hp q ⟨h.1⟩ P h.2).1 n i)).symm.toAddMonoidHom.comp
        ((castHs (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring)).comp (δ q (opn P.U) (n + 2 * d - 1) (i + d)))
      else 0
  have hrs : ∀ (q : ℕ) [NeZero q] (P : SP d) (_ : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ) u,
      pur q P n i (rs q P n i u) =
        castHs (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring) (δ q (opn P.U) (n + 2 * d - 1) (i + d) u) := by
    intro q _ P hq n i u
    simp only [rs, dif_pos (⟨NeZero.ne q, hq⟩ : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)))]
    exact AddEquiv.ofBijective_apply_symm_apply (pur q P n i) ((hp q P hq).1 n i)
  refine ⟨gys, rs, ?_⟩
  intro q _ P hq
  obtain ⟨hbij, hnat, hproj, hred⟩ := hp q P hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    have ex := hex q (opn P.U) (mono_opn _) (n + 2 * d - 1) (i + d)
    have ex' := hex q (opn P.U) (mono_opn _) (n + 2 * d) (i + d)
    refine ⟨?_, ?_, ?_⟩
    · intro x
      refine Iff.trans ?_ (ex.2.1 x)
      constructor
      · intro h
        have h2 := congrArg (pur q P n i) h
        rw [hrs q P hq, map_zero] at h2
        exact (castHs_bij _ _).1 (by rw [h2, map_zero])
      · intro h
        apply (hbij n i).1
        rw [hrs q P hq, h, map_zero, map_zero]
    · intro y
      refine (exact_cast (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring) _ ex.2.2 (pur q P n i y)).trans ?_
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, (hbij n i).1 ((hrs q P hq n i x).trans hx)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hrs q P hq n i x).symm⟩
    · intro z
      refine (ex'.1 z).trans ?_
      constructor
      · rintro ⟨s, rfl⟩
        obtain ⟨y, rfl⟩ := (hbij n i).2 s
        exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨_, rfl⟩
  · intro P' φ n i
    have hq' : IsUnit (q : Γ(P'.X, ⊤)) := by
      have := hq.map (φ.f.appTop).hom
      rwa [map_natCast] at this
    refine ⟨?_, ?_⟩
    · intro a
      change _ = Hs.fgt q (opn P'.U) _ _ (pur q P' n i _)
      rw [← hnat, fgt_pull]
      rfl
    · intro u
      apply ((hp q P' hq').1 n i).1
      rw [← hnat, hrs q P hq, hrs q P' hq', castHs_pull]
      exact congrArg _ (hnatδ q _ _ (opnMap φ.f _ _ φ.le) (mono_opn _) (mono_opn _) _ _ u)
  · exact hproj
  · intro r hr n i
    have : NeZero r := ⟨fun h => by subst h; exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hr)⟩
    have hr' : IsUnit (r : Γ(P.X, ⊤)) := by
      obtain ⟨k, hk⟩ := hr
      rw [hk, Nat.cast_mul] at hq
      exact isUnit_of_mul_isUnit_left hq
    refine ⟨?_, ?_⟩
    · intro a
      exact fgt_red _ _ _ _ (hred r hr n i a)
    · intro u
      apply ((hp r P hr').1 n i).1
      apply Subtype.ext
      rw [hrs r P hr', hred r hr, hrs q P hq]
      exact castHs_val _ _ _ _ (hredδ q r hr _ (mono_opn _) _ _ u)

end LateralTheory.CohomologicalPurity
