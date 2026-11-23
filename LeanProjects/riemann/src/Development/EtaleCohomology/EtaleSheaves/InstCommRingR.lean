import Development.EtaleCohomology.EtaleSheaves.EtaleChapterDTwo

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem inv_of {q : ℕ} {E E' : Spc} (f : E ⟶ E') (h : Inv q E') : Inv q E :=
  fun U ⟨x⟩ => h U ⟨(f.app _).app _ x⟩

structure Collected (q : ℕ) where
  R : ∀ E : Spc, Inv q E → Type 1
  ring : ∀ E h, CommRing (R E h)
  ι : ∀ {E : Spc} (h : Inv q E) (k : ℕ), letI := ring E h; Ht q E (2 * k) k →+ R E h
  π : ∀ {E : Spc} (h : Inv q E) (k : ℕ), letI := ring E h; R E h →+ Ht q E (2 * k) k
  map : ∀ {E E' : Spc} (_ : E ⟶ E') (h : Inv q E) (h' : Inv q E'), letI := ring E h; letI := ring E' h'; R E' h' →+* R E h
  π_ι : ∀ {E : Spc} (h : Inv q E) (k : ℕ) (a : Ht q E (2 * k) k), π h k (ι h k a) = a
  ι_one : ∀ {E : Spc} (h : Inv q E), letI := ring E h; ι h 0 ((one q E).cast (by simp) (by simp)) = 1
  ι_mul : ∀ {E : Spc} (h : Inv q E) (k l : ℕ) (a : Ht q E (2 * k) k) (b : Ht q E (2 * l) l), letI := ring E h
    ι h (k + l) ((cup q a b).cast (by push_cast; ring) (by push_cast; ring)) = ι h k a * ι h l b
  ι_cpow : ∀ {E : Spc} (h : Inv q E) (k : ℕ) (x : Ht q E 2 1), letI := ring E h
    ι h k (cpow q x k) = ι h 1 (x.cast (by simp) (by simp)) ^ k
  map_ι : ∀ {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (a : Ht q E' (2 * k) k),
    map f h h' (ι h' k a) = ι h k (pull _ f _ _ a)
  π_map : ∀ {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (r : R E' h'),
    π h k (map f h h' r) = pull _ f _ _ (π h' k r)

instance {q : ℕ} (P : Collected q) (E : Spc) (h : Inv q E) : CommRing (P.R E h) := P.ring E h

abbrev PB {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : Spc := pullback V (PGL.pr N)

abbrev PB.pr {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : PB V ⟶ E := pullback.fst V (PGL.pr N)

abbrev PB.line {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : PB V ⟶ ofCat (glCat 1) := pullback.snd V (PGL.pr N) ≫ PGL.line N

abbrev Collected.deg1 {q : ℕ} (P : Collected q) {E : Spc} (h : Inv q E) (x : Ht q E 2 1) : P.R E h := P.ι h 1 (x.cast (by simp) (by simp))

def IsChern {q : ℕ} (P : Collected q) {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j) : Prop :=
  P.ι h 0 (c 0) = 1 ∧ (∀ j, N < j → c j = 0) ∧
  ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
    P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) = 0

def newton {A : Type 1} [CommRing A] (c : ℕ → A) (k : ℕ) : A :=
  PowerSeries.coeff k (-(PowerSeries.X * PowerSeries.derivative A (PowerSeries.mk c)) * (PowerSeries.mk c).invOfUnit 1)

def LeafA6nat : Prop := DivisorNaturality

def LeafA6ring : Prop := DivisorRingCompatibility

def LeafA6supp : Prop := DivisorSupportCondition

def LeafRing : Prop := ∀ (q : ℕ) [NeZero q], Nonempty (Collected q)

def LeafChern : Prop := D1 → ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)),
  ∃! c, IsChern P h V c

def LeafNat : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') {N : ℕ}
  (V : E' ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E' (2 * j) j), IsChern P h' V c → IsChern P h (f ≫ V) fun j => pull _ f _ _ (c j)

def LocCover {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx E n X), ∃ S : Sieve X, S ∈ Scheme.etaleTopology X ∧ ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
    (∃ y : Sx U n Y, (f.app _).app _ y = (E.obj (op (SimplexCategory.mk n))).map k.op x) ∨
    (∃ y : Sx V n Y, (g.app _).app _ y = (E.obj (op (SimplexCategory.mk n))).map k.op x)

def LeafCover2 : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g → LocCover f g → Cover2 R f g

def LeafGeom : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₁ U₂ : Spc) (f₁ : U₁ ⟶ PB (bsumOf V W)) (f₂ : U₂ ⟶ PB (bsumOf V W)) (p₁ : U₁ ⟶ PB V) (p₂ : U₂ ⟶ PB W),
    Mono f₁ ∧ Mono f₂ ∧ LocCover f₁ f₂ ∧ p₁ ≫ PB.pr V = f₁ ≫ PB.pr _ ∧ p₁ ≫ PB.line V = f₁ ≫ PB.line _ ∧
    p₂ ≫ PB.pr W = f₂ ≫ PB.pr _ ∧ p₂ ≫ PB.line W = f₂ ≫ PB.line _

def LeafWhitney : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) {a b : ℕ} (V : E ⟶ ofCat (glCat a))
  (W : E ⟶ ofCat (glCat b)) (c d : ∀ j : ℕ, Ht q E (2 * j) j), IsChern P h V c → IsChern P h W d →
  ∃ e, IsChern P h (bsumOf V W) e ∧ ∀ k, P.ι h k (e k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2)

def LeafLine : Prop := ∀ (q : ℕ) [NeZero q] (P : Collected q) {E : Spc} (h : Inv q E) (L : E ⟶ ofCat (glCat 1))
  (c : ∀ j : ℕ, Ht q E (2 * j) j), IsChern P h L c → P.ι h 1 (c 1) = -P.deg1 h (c1 q L)

def LeafNewton : Prop :=
  (∀ (A B : Type 1) [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A), c 0 = 1 → ∀ k, φ (newton c k) = newton (fun j => φ (c j)) k) ∧
  (∀ (A : Type 1) [CommRing A] (c d e : ℕ → A), c 0 = 1 → d 0 = 1 → (∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) →
    ∀ k, newton e k = newton c k + newton d k) ∧
  ∀ (A : Type 1) [CommRing A] (c : ℕ → A) (x : A), c 0 = 1 → c 1 = -x → (∀ j, 1 < j → c j = 0) → ∀ k, 0 < k → newton c k = x ^ k

theorem goal_of (hR : LeafRing) (hC : LeafChern) (hN : LeafNat) (hW : LeafWhitney) (hL : LeafLine) (hS : LeafNewton) :
    LateralTheory.E.EtaleChapterDTwo := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD q _ k hk
  classical
  obtain ⟨P⟩ := hR q
  have hE := fun {E : Spc} (h : Inv q E) {N : ℕ} (V : E ⟶ ofCat (glCat N)) => hC hD q P h V
  choose c hc hu using @hE
  refine ⟨fun {E N} V => if h : Inv q E then P.π h k (newton (fun j => P.ι h j (c h V j)) k) else 0, ?_, ?_, ?_⟩
  · intro E E' N f V h'
    have h := inv_of f h'
    simp only [dif_pos h, dif_pos h']
    rw [← hu h (f ≫ V) _ (hN q P f h h' V _ (hc h' V)), ← P.π_map f h h', hS.1 _ _ _ _ (hc h' V).1]
    simp only [P.map_ι]
  · intro E a b V W h
    simp only [dif_pos h]
    obtain ⟨e, he, hk⟩ := hW q P h V W _ _ (hc h V) (hc h W)
    rw [← hu h _ e he, hS.2.1 _ (fun j => P.ι h j (c h V j)) (fun j => P.ι h j (c h W j)) _ (hc h V).1 (hc h W).1 hk, map_add]
  · intro E L h
    simp only [dif_pos h]
    rw [hS.2.2 _ _ _ (hc h L).1 (hL q P h L _ (hc h L)) (fun j hj => by rw [(hc h L).2.1 j hj, map_zero]) k hk,
      ← P.ι_cpow, P.π_ι]

end LateralTheory.E.D2
