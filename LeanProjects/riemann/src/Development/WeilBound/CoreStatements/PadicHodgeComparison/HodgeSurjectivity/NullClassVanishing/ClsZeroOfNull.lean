import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto.RKillOf3

open Pb HT CH

universe u v w

section Gen

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{w} R}
  (P : Pairing F₁ F₂ F₃)

theorem rel_right {Q : ObjectProperty C} (hQ : Cosieve Q) {p q n : ℕ} (h : p + q = n) (f : Cn F₁ p) {g : Cn F₂ q}
    (hg : g ∈ relS F₂ Q q) : P.cupC h f g ∈ relS F₃ Q n := fun s hs => by
  rw [CrystallineSemistableComparison.Auxff.cupC_apply]
  have : term F₂ s g (back h) (back_mono h) = 0 := by
    unfold term
    rw [hg _ (hQ (s.map (homOfLE (Fin.zero_le _))) hs), map_zero]
  rw [this, map_zero]

theorem null_of_B {Q : ObjectProperty C} (hQ : Cosieve Q) {p q N : ℕ} (h : p + q = N + 1) (f : Cn F₁ p)
    (hf : f ∈ (cx F₁).B p) {g : Cn F₂ q} (hg0 : d F₂ q g = 0) (hg : g ∈ relS F₂ Q q) :
    ∃ b ∈ relS F₃ Q N, d F₃ N b = P.cupC h f g := by
  cases p with
  | zero =>
    have hf0 : f = 0 := (Submodule.mem_bot R).1 hf
    subst hf0
    exact ⟨0, zero_mem _, by rw [map_zero, map_zero, LinearMap.zero_apply]⟩
  | succ m =>
    obtain ⟨β, rfl⟩ := LinearMap.mem_range.1 (hf : f ∈ LinearMap.range ((cx F₁).d m))
    refine ⟨P.cupC (p := m) (q := q) (by omega) β g, rel_right P hQ _ _ hg, ?_⟩
    rw [CrystallineSemistableComparison.P.leibniz, hg0, map_zero, smul_zero, add_zero]

theorem cupC_heq {p q n n' : ℕ} (e : n = n') (h : p + q = n) (h' : p + q = n') (f : Cn F₁ p) (g : Cn F₂ q) :
    HEq (P.cupC h f g) (P.cupC h' f g) := by
  subst e; rfl

end Gen

section Null

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F : C ⥤ ModuleCat.{w} R}

theorem cls_zero_of_null {Q : ObjectProperty C} : ∀ (n : ℕ) (z : Cn F n) (hz : d F n z = 0),
    RelNull F Q n z → (cx F).cls z hz = 0
  | 0, z, hz, h => by
    have h0 : z = 0 := h
    exact ((CrystallineSemistableComparison.P.cls_surj (cx F) 0).2.1 z hz).2 (by rw [h0]; exact zero_mem _)
  | n + 1, z, hz, h => by
    obtain ⟨b, -, hb⟩ := h
    exact ((CrystallineSemistableComparison.P.cls_surj (cx F) (n + 1)).2.1 z hz).2 (LinearMap.mem_range.2 ⟨b, hb⟩)

theorem null_succ {Q : ObjectProperty C} {M K : ℕ} (e : M = K + 1) (x : Cn F M) (x' : Cn F (K + 1))
    (hx : HEq x x') (h : RelNull F Q M x) : ∃ b ∈ relS F Q K, d F K b = x' := by
  subst e
  obtain rfl := eq_of_heq hx
  exact h

end Null

section Mul

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R}

theorem mul_assoc' {a₁ b₁ a₂ b₂ a₃ b₃ a₁₂ b₁₂ a₂₃ b₂₃ a₄ b₄ : IdF A}
    (h₁ : MulOk a₁ b₁ a₂ b₂ a₁₂ b₁₂) (h₂ : MulOk a₁₂ b₁₂ a₃ b₃ a₄ b₄) (h₃ : MulOk a₂ b₂ a₃ b₃ a₂₃ b₂₃)
    (h₄ : MulOk a₁ b₁ a₂₃ b₂₃ a₄ b₄) {T : C} (x : sqM a₁ b₁ T) (y : sqM a₂ b₂ T) (z : sqM a₃ b₃ T) :
    h₂.mul (h₁.mul x y) z = h₄.mul x (h₃.mul y z) := by
  obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
  obtain ⟨z, hz, rfl⟩ := sq_surj _ _ z
  rw [h₁.mul_mk, h₂.mul_mk, h₃.mul_mk, h₄.mul_mk]
  exact (sq_eq _ _ _ _).2 (by rw [mul_assoc, sub_self]; exact zero_mem _)

theorem cupC_assoc {a₁ b₁ a₂ b₂ a₃ b₃ a₁₂ b₁₂ a₂₃ b₂₃ a₄ b₄ : IdF A}
    (h₁ : MulOk a₁ b₁ a₂ b₂ a₁₂ b₁₂) (h₂ : MulOk a₁₂ b₁₂ a₃ b₃ a₄ b₄) (h₃ : MulOk a₂ b₂ a₃ b₃ a₂₃ b₂₃)
    (h₄ : MulOk a₁ b₁ a₂₃ b₂₃ a₄ b₄) {p q r m k n : ℕ} (g₁ : p + q = m) (g₂ : m + r = n) (g₃ : q + r = k)
    (g₄ : p + k = n) (f : Cn (sq a₁ b₁) p) (g : Cn (sq a₂ b₂) q) (l : Cn (sq a₃ b₃) r) :
    h₂.pair.cupC g₂ (h₁.pair.cupC g₁ f g) l = h₄.pair.cupC g₄ f (h₃.pair.cupC g₃ g l) := by
  funext s
  rw [CrystallineSemistableComparison.Auxff.cupC_apply, CrystallineSemistableComparison.Auxff.cupC_apply, CrystallineSemistableComparison.Auxff.term_cupC, CrystallineSemistableComparison.Auxff.term_cupC]
  show h₂.mul (h₁.mul _ _) _ = h₄.mul _ (h₃.mul _ _)
  refine (mul_assoc' h₁ h₂ h₃ h₄ _ _ _).trans ?_
  refine congrArg₂ (fun u v => h₄.mul u v) (term_congr _ _ _ _ _ ?_)
    (congrArg₂ (fun u v => h₃.mul u v) (term_congr _ _ _ _ _ ?_) (term_congr _ _ _ _ _ ?_)) <;>
    funext t <;> apply Fin.ext <;> (simp [front, back]; try omega)

end Mul

section Pull

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem sq_mk (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.Le a a') (hb : m.Le b b') (T : C')
    (x : Φ.A.obj (m.G.obj T)) (hx : x ∈ a.S _) :
    (m.sq ha hb).τ T (sqMk a b x hx) = sqMk a' b' (m.ρ T x) (ha T x hx) := rfl

theorem sq_mul (m : SMor Φ Φ' σ) {a b a' b' a'' b'' : IdF Φ.A} {c e c' e' c'' e'' : IdF Φ'.A}
    (h : MulOk a b a' b' a'' b'') (h' : MulOk c e c' e' c'' e'') (ha : m.Le a c) (hb : m.Le b e) (ha' : m.Le a' c')
    (hb' : m.Le b' e') (ha'' : m.Le a'' c'') (hb'' : m.Le b'' e'') (T : C') (x : sqM a b (m.G.obj T))
    (y : sqM a' b' (m.G.obj T)) :
    (m.sq ha'' hb'').τ T (h.mul x y) = h'.mul ((m.sq ha hb).τ T x) ((m.sq ha' hb').τ T y) := by
  obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
  rw [h.mul_mk, sq_mk, sq_mk, sq_mk, h'.mul_mk]
  exact (sq_eq _ _ _ _).2 (by rw [map_mul, sub_self]; exact zero_mem _)

theorem pullC_cupC (m : SMor Φ Φ' σ) {a b a' b' a'' b'' : IdF Φ.A} {c e c' e' c'' e'' : IdF Φ'.A}
    (h : MulOk a b a' b' a'' b'') (h' : MulOk c e c' e' c'' e'') (ha : m.Le a c) (hb : m.Le b e) (ha' : m.Le a' c')
    (hb' : m.Le b' e') (ha'' : m.Le a'' c'') (hb'' : m.Le b'' e'') {p q n : ℕ} (g : p + q = n) (f : Cn (sq a b) p)
    (k : Cn (sq a' b') q) :
    (m.sq ha'' hb'').pullC n (h.pair.cupC g f k) =
      h'.pair.cupC g ((m.sq ha hb).pullC p f) ((m.sq ha' hb').pullC q k) := by
  funext s
  show (m.sq ha'' hb'').τ _ (h.mul _ _) = h'.mul _ _
  rw [sq_mul m h h' ha hb ha' hb' ha'' hb'']
  exact congrArg₂ (fun x y => h'.mul x y) (CrystallineSemistableComparison.Auxff.term_pull (m.sq ha hb) s f _ _)
    (CrystallineSemistableComparison.Auxff.term_pull (m.sq ha' hb') s k _ _)

end Pull

section Main

variable {K : Type} [Field K] {Z Y : Scheme.{0}}

theorem pullC_cupC' {p : Z ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z) (hu : u ≫ p = q)
    {a a' c i j n : ℕ} (ha : a + a' = c) (h : i + j = n) (f : CH.Cn (G p a) i) (g : CH.Cn (G p a') j) :
    pullC u hu c n (cupC p ha h f g) = cupC q ha h (pullC u hu a i f) (pullC u hu a' j g) :=
  pullC_cupC (smS u hu) _ _ _ _ _ _ _ _ h f g

end Main

section Main2

variable {K : Type} [Field K] {Z Y : Scheme.{0}}

theorem pull_rel {W : Scheme.{0}} (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) {a n : ℕ}
    {z : CH.Cn (G q a) n} (hz : z ∈ relS (G q a) (On q i) n) :
    pullC π rfl a n z ∈ relS (G (π ≫ q) a) (On (π ≫ q) (pullback.snd i π)) n := fun s hs => by
  have h0 := hz (s ⋙ (smS π rfl).G) (((hS K W Z Y q i π).2.2.2.2.2 (s.obj 0)).1 hs)
  show (morG π rfl a).τ _ (z (s ⋙ (smS π rfl).G)) = 0
  rw [h0, map_zero]

theorem main (hS : SiteLaws) (hL : RelLift) (hI : RelInj) (hK : RelKill) (K : Type) [Field K] [CharZero K]
    (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] (i : W ⟶ Z) (π : Y ⟶ Z) [IsProper π]
    (D : E.LineData Y) (d : ℕ) (hd : 0 < d) (hB : Nonempty (Blow q i π D d)) (e : Hdg (π ≫ q) 1 2)
    (he : IsDlogFirstChernClass (π ≫ q) D e) (a n a' n' A N : ℕ) (hA : a + a' = A) (hN : n + n' = N) (c : Hdg q a n) (y : Hdg q a' n')
    (hc : pullH π rfl a n c = 0 ∨ ∃ (a₀ n₀ : ℕ) (ha : 1 + a₀ = a) (hn : 2 + n₀ = n) (w : Hdg (π ≫ q) a₀ n₀),
      pullH π rfl a n c = cupH (π ≫ q) ha hn e w)
    (hy : pullH i rfl a' n' y = 0) : cupH q hA hN c y = 0 := by
  have : IsClosedImmersion i := hB.some.closed
  have : Mono i := inferInstance
  obtain ⟨z, hz, hzr, rfl⟩ := hL K W Z q i a' n' y hy
  obtain ⟨c₀, hc₀, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 c
  have hSZ := hS K W Z Z q i (𝟙 Z)
  have hSY := hS K (pullback i π) Y Y (π ≫ q) (pullback.snd i π) (𝟙 Y)
  obtain ⟨hΓ, eΓ⟩ := CrystallineSemistableComparison.P.cup_cls (grOk (smFun Z q) hA).pair hN c₀ z hc₀ hz
  refine eΓ.trans (cls_zero_of_null (Q := On q i) N _ hΓ ?_)
  refine hI K W Z Y q i π D d hd hB A N _ hΓ (rel_right _ hSZ.2.1 _ _ hzr) ?_
  have ep : pullC π rfl A N (cupC q hA hN c₀ z) = cupC (π ≫ q) hA hN (pullC π rfl a n c₀) (pullC π rfl a' n' z) :=
    pullC_cupC' π rfl hA hN c₀ z
  change RelNull (G (π ≫ q) A) (On (π ≫ q) (pullback.snd i π)) N (pullC π rfl A N (cupC q hA hN c₀ z))
  rw [ep]
  have hz' : CH.d (G (π ≫ q) a') n' (pullC π rfl a' n' z) = 0 := by
    rw [show CH.d (G (π ≫ q) a') n' (pullC π rfl a' n' z) = pullC π rfl a' (n' + 1) (CH.d (G q a') n' z) from
      (morG π rfl a').d_pullC n' z, hz, map_zero]
  have hzr' := pull_rel hS q i π hzr
  have hpc : CH.d (G (π ≫ q) a) n (pullC π rfl a n c₀) = 0 := by
    rw [show CH.d (G (π ≫ q) a) n (pullC π rfl a n c₀) = pullC π rfl a (n + 1) (CH.d (G q a) n c₀) from
      (morG π rfl a).d_pullC n c₀, hc₀, map_zero]
  have epc : pullH π rfl a n ((CH.cx (G q a)).cls c₀ hc₀) = (CH.cx (G (π ≫ q) a)).cls (pullC π rfl a n c₀) hpc := rfl
  rcases N with _ | N'
  · obtain rfl : n = 0 := by omega
    obtain rfl : n' = 0 := by omega
    rcases hc with hc | ⟨a₀, n₀, ha, hn, w, -⟩
    · rw [epc] at hc
      have h0 : pullC π rfl a 0 c₀ = 0 :=
        (Submodule.mem_bot K).1 (((CrystallineSemistableComparison.P.cls_surj _ 0).2.1 _ hpc).1 hc)
      show cupC (π ≫ q) hA hN (pullC π rfl a 0 c₀) (pullC π rfl a' 0 z) = 0
      rw [h0, map_zero, LinearMap.zero_apply]
    · omega
  · rcases hc with hc | ⟨a₀, n₀, ha, hn, w, hw⟩
    · rw [epc] at hc
      exact null_of_B _ hSY.2.1 hN _ (((CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hpc).1 hc) hz' hzr'
    · subst ha
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨1 + n₀, by omega⟩
      have hA' : 1 + (a₀ + a') = A := by omega
      subst hA'
      obtain ⟨r, hr, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ 2).1 e
      obtain ⟨w₀, hw₀, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n₀).1 w
      obtain ⟨hrw, erw⟩ := CrystallineSemistableComparison.P.cup_cls (grOk (smFun Y (π ≫ q)) (rfl : 1 + a₀ = 1 + a₀)).pair hn r w₀ hr hw₀
      rw [epc] at hw
      have hdiff := ((CrystallineSemistableComparison.P.cls_surj _ (m + 1)).2.2.1 _ _ hpc hrw).1 (hw.trans erw)
      obtain ⟨b₁, hb₁r, hb₁⟩ := null_of_B _ hSY.2.1 hN _ hdiff hz' hzr'
      obtain ⟨hX, -⟩ := CrystallineSemistableComparison.P.cup_cls (grOk (smFun Y (π ≫ q)) (rfl : a₀ + a' = a₀ + a')).pair
        (rfl : n₀ + n' = n₀ + n') w₀ (pullC π rfl a' n' z) hw₀ hz'
      have hXr := rel_right (grOk (smFun Y (π ≫ q)) (rfl : a₀ + a' = a₀ + a')).pair hSY.2.1
        (rfl : n₀ + n' = n₀ + n') w₀ hzr'
      have hk := hK K W Z Y q i π D d hd hB r hr he (a₀ + a') (n₀ + n') _ hX hXr
      obtain ⟨b₂, hb₂r, hb₂⟩ := null_succ (by omega : 2 + (n₀ + n') = N' + 1) _
        ((grOk (smFun Y (π ≫ q)) (rfl : 1 + (a₀ + a') = 1 + (a₀ + a'))).pair.cupC (p := 2) (q := n₀ + n')
          (by omega) r ((grOk (smFun Y (π ≫ q)) (rfl : a₀ + a' = a₀ + a')).pair.cupC rfl w₀ (pullC π rfl a' n' z)))
        (cupC_heq _ (by omega) _ _ _ _) hk
      refine ⟨b₁ + b₂, add_mem hb₁r hb₂r, ?_⟩
      rw [map_add, hb₁, hb₂]
      have ea := cupC_assoc (grOk (smFun Y (π ≫ q)) (rfl : 1 + a₀ = 1 + a₀))
        (grOk (smFun Y (π ≫ q)) hA) (grOk (smFun Y (π ≫ q)) (rfl : a₀ + a' = a₀ + a'))
        (grOk (smFun Y (π ≫ q)) (rfl : 1 + (a₀ + a') = 1 + (a₀ + a'))) hn hN (rfl : n₀ + n' = n₀ + n') (by omega)
        r w₀ (pullC π rfl a' n' z)
      show _ + _ = cupC (π ≫ q) hA hN (pullC π rfl (1 + a₀) (m + 1) c₀) (pullC π rfl a' n' z)
      conv_rhs => rw [show pullC π rfl (1 + a₀) (m + 1) c₀ =
        (pullC π rfl (1 + a₀) (m + 1) c₀ - cupC (π ≫ q) rfl hn r w₀) + cupC (π ≫ q) rfl hn r w₀ by abel]
      rw [map_add, LinearMap.add_apply]
      exact congrArg₂ (· + ·) rfl ea.symm

end Main2

end CrystallineSemistableComparison.Onto.RKillOf3

theorem CrystallineSemistableComparison.Onto.killOf3_pf : CrystallineSemistableComparison.Onto.KillOf3 := by
  intro hS _ hL hI hK K _ _ W Z Y q _ _ i π _ D d hd hB e he a n a' n' c y hc hy
  exact CrystallineSemistableComparison.Onto.RKillOf3.main hS hL hI hK K W Z Y q i π D d hd hB e he a n a' n' _ _ rfl rfl c y hc hy
