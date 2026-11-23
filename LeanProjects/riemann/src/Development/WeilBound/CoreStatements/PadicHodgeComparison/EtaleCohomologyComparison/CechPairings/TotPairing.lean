import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotalComplexPairingSign
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace CrystallineSemistableComparison.Auxff
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH

theorem term_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {p m n : ℕ}
    (s : ComposableArrows C n) (f : Cn F p)
    (g : Fin (m + 1) → Fin (n + 1)) (hg : Monotone g) (k : Fin (p + 1) → Fin (m + 1)) (hk : Monotone k) :
    (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last m)))))).hom (term F (hg.functor ⋙ s) f k hk) =
      term F s f (g ∘ k) (hg.comp hk) := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last (k (Fin.last p)))) ≫ s.map (homOfLE (Fin.le_last (g (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (g (k (Fin.last p))))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  show (F.map ((hg.functor ⋙ s).map (homOfLE (Fin.le_last (k (Fin.last p))))) ≫
    F.map (s.map (homOfLE (Fin.le_last (g (Fin.last m)))))).hom (f ((hg.comp hk).functor ⋙ s)) = _
  rw [← F.map_comp, e]
  rfl

theorem term_d {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {p n : ℕ}
    (s : ComposableArrows C n) (f : Cn F p)
    (g : Fin (p + 2) → Fin (n + 1)) (hg : Monotone g) :
    term F s (d F p f) g hg = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
      term F s f (g ∘ i.succAbove) (hg.comp (Fin.strictMono_succAbove i).monotone) := by
  have e : d F p f (hg.functor ⋙ s) = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
      term F (hg.functor ⋙ s) f i.succAbove (Fin.strictMono_succAbove i).monotone := rfl
  show (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last (p + 1))))))).hom (d F p f (hg.functor ⋙ s)) = _
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, term_comp]

theorem cupC_apply {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ : C ⥤ ModuleCat.{w} R}
    {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n)
    (f : Cn F₁ p) (g : Cn F₂ q) (s : ComposableArrows C n) :
    P.cupC h f g s = P.μ _ (term F₁ s f (front h) (front_mono h)) (term F₂ s g (back h) (back_mono h)) := rfl

theorem sum_split {M : Type*} [AddCommMonoid M] {N a b : ℕ} (e : N = a + b) (φ : Fin N → M) :
    ∑ i, φ i = ∑ j : Fin a, φ (Fin.cast e.symm (Fin.castAdd b j)) + ∑ k : Fin b, φ (Fin.cast e.symm (Fin.natAdd a k)) := by
  subst e; simp [Fin.sum_univ_add]

theorem sa_val {N : ℕ} (i : Fin (N + 1)) (t : Fin N) : (i.succAbove t : ℕ) = if (t : ℕ) < i then (t : ℕ) else t + 1 := by
  rcases lt_or_ge (t : ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]; simp; omega

theorem four {M : Type*} [AddCommGroup M] {x y A B a b : M} (h1 : x = A) (h2 : y = B) (h3 : a + b = 0) :
    x + y = (A + a) + (b + B) := by
  subst h1 h2; rw [eq_neg_of_add_eq_zero_left h3]; abel

end CrystallineSemistableComparison.Auxff

theorem CrystallineSemistableComparison.P.leibniz : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n) (f : Cn F₁ p) (g : Cn F₂ q), d F₃ n (P.cupC h f g) = P.cupC (p := p + 1) (q := q) (by omega) (d F₁ p f) g + (-1 : ℤ) ^ p • P.cupC (p := p) (q := q + 1) (by omega) f (d F₂ q g) := by
  intro R _ C _ F₁ F₂ F₃ P p q n h f g
  subst h
  funext s
  have hL : d F₃ (p + q) (P.cupC rfl f g) s = ∑ i : Fin (p + q + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.μ _ (term F₁ s f (i.succAbove ∘ front (rfl : p + q = p + q)) ((Fin.strictMono_succAbove i).monotone.comp (front_mono _)))
        (term F₂ s g (i.succAbove ∘ back (rfl : p + q = p + q)) ((Fin.strictMono_succAbove i).monotone.comp (back_mono _))) := by
    show ∑ i : Fin (p + q + 2), (-1 : ℤ) ^ (i : ℕ) • (F₃.map (GlobalTheory.CatH.toLast i s)).hom (P.cupC rfl f g (GlobalTheory.CatH.face i s)) = _
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CrystallineSemistableComparison.Auxff.cupC_apply, ← P.nat, term_face, term_face]
  rw [hL, Pi.add_apply, Pi.smul_apply, CrystallineSemistableComparison.Auxff.cupC_apply, CrystallineSemistableComparison.Auxff.cupC_apply, CrystallineSemistableComparison.Auxff.term_d, CrystallineSemistableComparison.Auxff.term_d]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [CrystallineSemistableComparison.Auxff.sum_split (show p + q + 2 = (p + 1) + (q + 1) by omega), Fin.sum_univ_castSucc (n := p + 1),
    Fin.sum_univ_succ (n := q + 1), smul_add, Finset.smul_sum]
  refine CrystallineSemistableComparison.Auxff.four (Finset.sum_congr rfl fun j _ => ?_) (Finset.sum_congr rfl fun k _ => ?_) ?_
  · congr 1
    refine congrArg₂ (fun x y => P.μ _ x y) (term_congr _ _ _ _ _ ?_) (term_congr _ _ _ _ _ ?_) <;>
        funext t <;> apply Fin.ext <;> simp only [Function.comp, CrystallineSemistableComparison.Auxff.sa_val, front, back, Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ, Fin.val_last, Fin.val_zero] <;> split_ifs <;> omega
  · rw [smul_smul, ← pow_add]
    congr 1
    · congr 1; simp; omega
    · refine congrArg₂ (fun x y => P.μ _ x y) (term_congr _ _ _ _ _ ?_) (term_congr _ _ _ _ _ ?_) <;>
        funext t <;> apply Fin.ext <;> simp only [Function.comp, CrystallineSemistableComparison.Auxff.sa_val, front, back, Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ, Fin.val_last, Fin.val_zero] <;> split_ifs <;> omega
  · rw [smul_smul, ← pow_add, add_eq_zero_iff_eq_neg, ← neg_smul]
    congr 1
    · simp [pow_succ]
    · refine congrArg₂ (fun x y => P.μ _ x y) (term_congr _ _ _ _ _ ?_) (term_congr _ _ _ _ _ ?_) <;>
        funext t <;> apply Fin.ext <;> simp only [Function.comp, CrystallineSemistableComparison.Auxff.sa_val, front, back, Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ, Fin.val_last, Fin.val_zero] <;> split_ifs <;> omega

namespace CrystallineSemistableComparison.Auxff
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH

theorem cls_out {R : Type} [CommRing R] (K : Cx.{w} R) {n : ℕ} (x : K.H n) :
    K.cls (Quotient.out x).1 (Quotient.out x).2 = x := Quotient.out_eq x

theorem memB_left {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (P : CxPairing K L M)
    {p q n : ℕ} (h : p + q = n) (x : K.X p) (hx : x ∈ K.B p) (b : L.X q) (hb : L.d q b = 0) : P.μ h x b ∈ M.B n := by
  rcases p with _ | p
  · have : x = 0 := hx
    rw [this, map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + q, by omega⟩
    obtain ⟨u, rfl⟩ := hx
    refine ⟨P.μ (p := p) (q := q) (by omega) u b, ?_⟩
    rw [P.leib, hb, map_zero, smul_zero, add_zero]

theorem memB_right {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (P : CxPairing K L M)
    {p q n : ℕ} (h : p + q = n) (a : K.X p) (ha : K.d p a = 0) (y : L.X q) (hy : y ∈ L.B q) : P.μ h a y ∈ M.B n := by
  rcases q with _ | q
  · have : y = 0 := hy
    rw [this, map_zero]; exact Submodule.zero_mem _
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + q, by omega⟩
    obtain ⟨v, rfl⟩ := hy
    refine ⟨(-1 : ℤ) ^ p • P.μ (p := p) (q := q) (by omega) a v, ?_⟩
    rw [map_zsmul, P.leib, ha, map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
    simp

end CrystallineSemistableComparison.Auxff

theorem CrystallineSemistableComparison.P.cxcup_cls : ∀ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (P : CxPairing K L M) {p q n : ℕ} (h : p + q = n) (a : K.X p) (b : L.X q) ha hb hc, P.cup h (K.cls a ha) (L.cls b hb) = M.cls (P.μ h a b) hc := by
  intro R _ K L M P p q n h a b ha hb hc
  unfold CxPairing.cup
  rw [(CrystallineSemistableComparison.P.cls_surj M n).2.2.1]
  have h1 : (Quotient.out (K.cls a ha)).1 - a ∈ K.B p :=
    ((CrystallineSemistableComparison.P.cls_surj K p).2.2.1 _ _ _ ha).mp (CrystallineSemistableComparison.Auxff.cls_out K _)
  have h2 : (Quotient.out (L.cls b hb)).1 - b ∈ L.B q :=
    ((CrystallineSemistableComparison.P.cls_surj L q).2.2.1 _ _ _ hb).mp (CrystallineSemistableComparison.Auxff.cls_out L _)
  have e : P.μ h (Quotient.out (K.cls a ha)).1 (Quotient.out (L.cls b hb)).1 - P.μ h a b =
      P.μ h ((Quotient.out (K.cls a ha)).1 - a) (Quotient.out (L.cls b hb)).1 +
        P.μ h a ((Quotient.out (L.cls b hb)).1 - b) := by
    simp only [map_sub, LinearMap.sub_apply]; abel
  rw [e]
  exact add_mem (CrystallineSemistableComparison.Auxff.memB_left P h _ h1 _ (Quotient.out (L.cls b hb)).2)
    (CrystallineSemistableComparison.Auxff.memB_right P h a ha _ h2)

namespace CrystallineSemistableComparison.Auxff
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH

noncomputable def toCx {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ : C ⥤ ModuleCat.{w} R}
    {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃) :
    CxPairing (cx F₁) (cx F₂) (cx F₃) where
  μ h := P.cupC h
  leib h x y := CrystallineSemistableComparison.P.leibniz P h x y

theorem cup_eq {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ : C ⥤ ModuleCat.{w} R}
    {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n)
    (x : H F₁ p) (y : H F₂ q) : P.cup h x y = (toCx P).cup h x y := by
  unfold Pairing.cup CxPairing.cup
  split_ifs with hz
  · rfl
  · exact absurd ((toCx P).leib h _ _ |>.trans (by
      rw [show d F₁ p (Quotient.out x).1 = 0 from (Quotient.out x).2,
        show d F₂ q (Quotient.out y).1 = 0 from (Quotient.out y).2]; simp)) hz

theorem closed {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (Q : CxPairing K L M)
    {p q n : ℕ} (h : p + q = n) (a : K.X p) (b : L.X q) (ha : K.d p a = 0) (hb : L.d q b = 0) :
    M.d n (Q.μ h a b) = 0 := by
  rw [Q.leib, ha, hb]; simp

theorem cx_bilin {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (Q : CxPairing K L M)
    {p q n : ℕ} (h : p + q = n) : ∃ b : K.H p →ₗ[R] L.H q →ₗ[R] M.H n, ∀ x y, b x y = Q.cup h x y := by
  have cc : ∀ (a : K.X p) (b : L.X q) ha hb, Q.cup h (K.cls a ha) (L.cls b hb) = M.cls (Q.μ h a b) (closed Q h a b ha hb) :=
    fun a b ha hb => CrystallineSemistableComparison.P.cxcup_cls Q h a b ha hb _
  refine ⟨LinearMap.mk₂ R (fun x y => Q.cup h x y) ?_ ?_ ?_ ?_, fun x y => rfl⟩
  · intro x x' y
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K p).1 x
    obtain ⟨a', ha', rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K p).1 x'
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L q).1 y
    have hs : K.d p (a + a') = 0 := by rw [map_add, ha, ha', add_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj K p).2.2.2.1 a a' ha ha' hs, cc, cc, cc]
    simp only [map_add, LinearMap.add_apply]
    exact (CrystallineSemistableComparison.P.cls_surj M n).2.2.2.1 _ _ _ _ _
  · intro r x y
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K p).1 x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L q).1 y
    have hs : K.d p (r • a) = 0 := by rw [map_smul, ha, smul_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj K p).2.2.2.2 r a ha hs, cc, cc]
    simp only [map_smul, LinearMap.smul_apply]
    exact (CrystallineSemistableComparison.P.cls_surj M n).2.2.2.2 _ _ _ _
  · intro x y y'
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K p).1 x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L q).1 y
    obtain ⟨b', hb', rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L q).1 y'
    have hs : L.d q (b + b') = 0 := by rw [map_add, hb, hb', add_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj L q).2.2.2.1 b b' hb hb' hs, cc, cc, cc]
    simp only [map_add]
    exact (CrystallineSemistableComparison.P.cls_surj M n).2.2.2.1 _ _ _ _ _
  · intro r x y
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K p).1 x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L q).1 y
    have hs : L.d q (r • b) = 0 := by rw [map_smul, hb, smul_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj L q).2.2.2.2 r b hb hs, cc, cc]
    simp only [map_smul]
    exact (CrystallineSemistableComparison.P.cls_surj M n).2.2.2.2 _ _ _ _

end CrystallineSemistableComparison.Auxff

theorem CrystallineSemistableComparison.P.cup_cls : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n) (a : Cn F₁ p) (b : Cn F₂ q) ha hb, ∃ hc, P.cup h ((cx F₁).cls a ha) ((cx F₂).cls b hb) = (cx F₃).cls (P.cupC h a b) hc := by
  intro R _ C _ F₁ F₂ F₃ P p q n h a b ha hb
  exact ⟨CrystallineSemistableComparison.Auxff.closed (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb,
    (CrystallineSemistableComparison.Auxff.cup_eq P h _ _).trans (CrystallineSemistableComparison.P.cxcup_cls (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb _)⟩

theorem CrystallineSemistableComparison.P.cup_bilin : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n), ∃ b : H F₁ p →ₗ[R] H F₂ q →ₗ[R] H F₃ n, ∀ x y, b x y = P.cup h x y := by
  intro R _ C _ F₁ F₂ F₃ P p q n h
  obtain ⟨b, hb⟩ := CrystallineSemistableComparison.Auxff.cx_bilin (CrystallineSemistableComparison.Auxff.toCx P) h
  exact ⟨b, fun x y => (hb x y).trans (CrystallineSemistableComparison.Auxff.cup_eq P h x y).symm⟩

namespace CrystallineSemistableComparison.Auxff
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH

theorem cls_congr {R : Type} [CommRing R] (K : Cx.{w} R) {n : ℕ} {a b : K.X n} (e : a = b) (ha : K.d n a = 0)
    (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst e; rfl

theorem cxmap {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R}
    {K' : Cx.{t} R'} {L' : Cx.{t'} R'} {M' : Cx.{u} R'} (P : CxPairing K L M) (Q : CxPairing K' L' M')
    (a : Cx.Hom K K' σ) (b : Cx.Hom L L' σ) (c : Cx.Hom M M' σ)
    (hc : ∀ {p q n : ℕ} (h : p + q = n) x y, c.f n (P.μ h x y) = Q.μ h (a.f p x) (b.f q y))
    {p q n : ℕ} (h : p + q = n) (x : K.H p) (y : L.H q) :
    c.mapH n (P.cup h x y) = Q.cup h (a.mapH p x) (b.mapH q y) := by
  obtain ⟨a0, ha0, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K p).1 x
  obtain ⟨b0, hb0, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L q).1 y
  have ha1 : K'.d p (a.f p a0) = 0 := by rw [a.comm, ha0, map_zero]
  have hb1 : L'.d q (b.f q b0) = 0 := by rw [b.comm, hb0, map_zero]
  have hc1 : M'.d n (c.f n (P.μ h a0 b0)) = 0 := by rw [c.comm, closed P h a0 b0 ha0 hb0, map_zero]
  rw [CrystallineSemistableComparison.P.cxcup_cls P h a0 b0 ha0 hb0 (closed P h a0 b0 ha0 hb0), CrystallineSemistableComparison.P.mapH_cls a p a0 ha0 ha1,
    CrystallineSemistableComparison.P.mapH_cls b q b0 hb0 hb1, CrystallineSemistableComparison.P.cxcup_cls Q h _ _ ha1 hb1 (closed Q h _ _ ha1 hb1),
    CrystallineSemistableComparison.P.mapH_cls c n _ _ hc1]
  exact cls_congr _ (hc h a0 b0) _ _

theorem term_pull {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} (m : Mor F F' σ)
    {p n : ℕ} (s : ComposableArrows C' n) (f : Cn F p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    m.τ _ (term F (s ⋙ m.G) f g hg) = term F' s (m.pullC p f) g hg :=
  m.nat _ _

theorem term_cupC {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ : C ⥤ ModuleCat.{w} R}
    {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} (P : Pairing F₁ F₂ F₃) {p q a m : ℕ} (h : p + q = a)
    (s : ComposableArrows C m) (f : Cn F₁ p) (g : Cn F₂ q) (k : Fin (a + 1) → Fin (m + 1)) (hk : Monotone k) :
    term F₃ s (P.cupC h f g) k hk = P.μ _ (term F₁ s f (k ∘ front h) (hk.comp (front_mono h)))
      (term F₂ s g (k ∘ back h) (hk.comp (back_mono h))) := by
  exact (P.nat (s.map (homOfLE (Fin.le_last (k (Fin.last a))))) _ _).symm.trans
    (congrArg₂ (fun x y => P.μ _ x y) (term_comp F₁ s f k hk (front h) (front_mono h))
      (term_comp F₂ s g k hk (back h) (back_mono h)))

theorem term_id {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {n : ℕ}
    (s : ComposableArrows C n) (f : Cn F n) (g : Fin (n + 1) → Fin (n + 1)) (hg : Monotone g) (e : ∀ t, (g t : ℕ) = t) :
    term F s f g hg = f s := by
  rw [term_congr F s f hg monotone_id (funext fun t => Fin.ext (e t))]
  show (F.map (s.map (𝟙 _))).hom (f s) = f s
  simp

theorem term_one {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) {m : ℕ}
    (s : ComposableArrows C m) (g : Fin 1 → Fin (m + 1)) (hg : Monotone g) :
    term (modF A) s (fun s => (1 : A.obj (s.obj (Fin.last 0)))) g hg = (1 : A.obj (s.obj (Fin.last m))) := by
  simp [term, modF]

theorem unit_left {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) {n : ℕ}
    (f : Cn (modF A) n) : (mulP A).cupC (Nat.zero_add n) (fun s => (1 : A.obj (s.obj (Fin.last 0)))) f = f := by
  funext s
  rw [cupC_apply]
  exact (congrArg₂ (fun u v : A.obj (s.obj (Fin.last n)) => u * v) (term_one A s _ _)
    (term_id _ s f _ _ (fun t => by simp [back]))).trans (one_mul _)

theorem unit_right {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R) {n : ℕ}
    (f : Cn (modF A) n) : (mulP A).cupC (Nat.add_zero n) f (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = f := by
  funext s
  rw [cupC_apply]
  exact (congrArg₂ (fun u v : A.obj (s.obj (Fin.last n)) => u * v)
    (term_id _ s f _ _ (fun t => by simp [front])) (term_one A s _ _)).trans (mul_one _)

theorem assoc {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R)
    {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n) (h₃ : q + r = b) (h₄ : p + b = n)
    (f : Cn (modF A) p) (g : Cn (modF A) q) (k : Cn (modF A) r) :
    (mulP A).cupC h₂ ((mulP A).cupC h₁ f g) k = (mulP A).cupC h₄ f ((mulP A).cupC h₃ g k) := by
  funext s
  rw [cupC_apply, cupC_apply, term_cupC, term_cupC]
  refine (mul_assoc (G := A.obj (s.obj (Fin.last n))) _ _ _).trans ?_
  refine congrArg₂ (fun u v : A.obj (s.obj (Fin.last n)) => u * v) (term_congr _ _ _ _ _ ?_) (congrArg₂ (fun u v : A.obj (s.obj (Fin.last n)) => u * v) (term_congr _ _ _ _ _ ?_) (term_congr _ _ _ _ _ ?_)) <;>
    funext t <;> apply Fin.ext <;> simp [front, back] <;> omega

end CrystallineSemistableComparison.Auxff

theorem CrystallineSemistableComparison.P.cup_pull : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R} {E₁ : C' ⥤ ModuleCat.{t} R'} {E₂ : C' ⥤ ModuleCat.{t'} R'} {E₃ : C' ⥤ ModuleCat.{u''} R'} (P : Pairing F₁ F₂ F₃) (Q : Pairing E₁ E₂ E₃) (G : C' ⥤ C) (τ₁ : ∀ T, F₁.obj (G.obj T) →ₛₗ[σ] E₁.obj T) (τ₂ : ∀ T, F₂.obj (G.obj T) →ₛₗ[σ] E₂.obj T) (τ₃ : ∀ T, F₃.obj (G.obj T) →ₛₗ[σ] E₃.obj T) h₁ h₂ h₃, (∀ T x y, τ₃ T (P.μ _ x y) = Q.μ T (τ₁ T x) (τ₂ T y)) → ∀ {p q n : ℕ} (h : p + q = n) x y, (Mor.mk G τ₃ h₃ : Mor F₃ E₃ σ).pull n (P.cup h x y) = Q.cup h ((Mor.mk G τ₁ h₁ : Mor F₁ E₁ σ).pull p x) ((Mor.mk G τ₂ h₂ : Mor F₂ E₂ σ).pull q y) := by
  intro R R' _ _ σ C _ C' _ F₁ F₂ F₃ E₁ E₂ E₃ P Q G τ₁ τ₂ τ₃ h₁ h₂ h₃ hμ p q n h x y
  rw [CrystallineSemistableComparison.Auxff.cup_eq, CrystallineSemistableComparison.Auxff.cup_eq]
  refine CrystallineSemistableComparison.Auxff.cxmap (CrystallineSemistableComparison.Auxff.toCx P) (CrystallineSemistableComparison.Auxff.toCx Q) (Mor.mk G τ₁ h₁ : Mor F₁ E₁ σ).hom
    (Mor.mk G τ₂ h₂ : Mor F₂ E₂ σ).hom (Mor.mk G τ₃ h₃ : Mor F₃ E₃ σ).hom ?_ h x y
  intro p q n h f g
  funext s
  exact (hμ _ _ _).trans (congrArg₂ (fun a b => Q.μ _ a b)
    (CrystallineSemistableComparison.Auxff.term_pull (Mor.mk G τ₁ h₁ : Mor F₁ E₁ σ) s f _ _)
    (CrystallineSemistableComparison.Auxff.term_pull (Mor.mk G τ₂ h₂ : Mor F₂ E₂ σ) s g _ _))

theorem CrystallineSemistableComparison.P.cup_ring : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R), (∀ n (x : H (modF A) n), (mulP A).cup (Nat.zero_add n) (oneH A) x = x ∧ (mulP A).cup (Nat.add_zero n) x (oneH A) = x) ∧ ∀ {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n) (h₃ : q + r = b) (h₄ : p + b = n) x y z, (mulP A).cup h₂ ((mulP A).cup h₁ x y) z = (mulP A).cup h₄ x ((mulP A).cup h₃ y z) := by
  intro R _ C _ A
  refine ⟨fun n x => ?_, fun {p q r a b n} h₁ h₂ h₃ h₄ x y z => ?_⟩
  · obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (modF A)) n).1 x
    constructor
    · obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (mulP A) (Nat.zero_add n) (fun s => (1 : A.obj (s.obj (Fin.last 0)))) f
        (oneH._proof_1 A) hf
      exact e.trans (CrystallineSemistableComparison.Auxff.cls_congr _ (CrystallineSemistableComparison.Auxff.unit_left A f) _ _)
    · obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (mulP A) (Nat.add_zero n) f (fun s => (1 : A.obj (s.obj (Fin.last 0))))
        hf (oneH._proof_1 A)
      exact e.trans (CrystallineSemistableComparison.Auxff.cls_congr _ (CrystallineSemistableComparison.Auxff.unit_right A f) _ _)
  · obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (modF A)) p).1 x
    obtain ⟨g, hg, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (modF A)) q).1 y
    obtain ⟨k, hk, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (modF A)) r).1 z
    obtain ⟨c1, e1⟩ := CrystallineSemistableComparison.P.cup_cls (mulP A) h₁ f g hf hg
    obtain ⟨c3, e3⟩ := CrystallineSemistableComparison.P.cup_cls (mulP A) h₃ g k hg hk
    rw [e1, e3]
    obtain ⟨c2, e2⟩ := CrystallineSemistableComparison.P.cup_cls (mulP A) h₂ _ k c1 hk
    obtain ⟨c4, e4⟩ := CrystallineSemistableComparison.P.cup_cls (mulP A) h₄ f _ hf c3
    rw [e2, e4]
    exact CrystallineSemistableComparison.Auxff.cls_congr _ (CrystallineSemistableComparison.Auxff.assoc A h₁ h₂ h₃ h₄ f g k) _ _
