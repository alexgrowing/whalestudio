import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedTrans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.RhoA

open Pb GlobalTheory.CompanionTheory.LiftLat

section Gr
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem pow_tf (c : b.R) (r : ℤ)
    (hT : ∀ (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (n : ℕ)
    (T : Q.FullSubcategory) (x : (sP Q).A.obj T) (h : c ^ n • x ∈ (sFil Q r).S T) : x ∈ (sFil Q r).S T := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact hT T x (ih _ h)

theorem gr_part (c : b.R) (r : ℕ)
    (hT : ∀ (r : ℤ) (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (j k : ℕ)
    (h1 : ∀ (x : HG Q r (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : HG Q r j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → HG Q r j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : HG Q r j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) :
    (∀ x : ∀ n, HGm Q (c ^ n) r j, (∀ n, trG Q c n r j (x (n + 1)) = x n) →
      ∃ z : HG Q r j, ∀ n, redG' Q (c ^ n) r j z = c ^ (2 * k) • x n) ∧
    ∀ z : HG Q r j, (∀ n, redG' Q (c ^ n) r j z = 0) → c ^ k • z = 0 := by
  have hle : ∀ T : Q.FullSubcategory, (sFil Q ((r : ℤ) + 1)).S T ≤ (sFil Q r).S T := fun T => T.obj.pdPow_anti (Nat.le_succ r)
  let red := fun n : ℕ => sqLe (a := sFil Q r) (b := sFil Q ((r : ℤ) + 1)) (a' := stdI Q (some (r : ℤ)) (c ^ n))
    (b' := stdI Q (some ((r : ℤ) + 1)) (c ^ n)) (fun _ => le_sup_left) fun _ => le_sup_left
  let tr := fun n : ℕ => sqLe (stdI_le Q (some (r : ℤ)) c n) (stdI_le Q (some ((r : ℤ) + 1)) c n)
  refine gen (G := fun n => sq (stdI Q (some (r : ℤ)) (c ^ n)) (stdI Q (some ((r : ℤ) + 1)) (c ^ n))) c red tr
    (fun n T => (red n).τ T) (fun n T => (tr n).τ T) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ?_ ?_ ?_ ?_ j k h1 h2 h3
  · intro n T x
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
    rfl
  · intro n T y
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
    obtain ⟨u, hu⟩ := (mem_some Q r _ T y).1 hy
    refine ⟨sqMk _ _ _ hu, (sq_eq _ _ (Ideal.mem_sup_left hu) hy).2 ((mem_some Q _ _ T _).2 ⟨-u, ?_⟩)⟩
    rw [smul_neg, show y - c ^ n • u - y - -(c ^ n • u) = 0 by abel]
    exact zero_mem _
  · intro n T x
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e1 : (red n).τ T (sqMk _ _ w hw) = 0 ↔ w ∈ (stdI Q (some ((r : ℤ) + 1)) (c ^ n)).S T :=
      sqMk_eq_zero (stdI Q (some (r : ℤ)) (c ^ n)) _ w (Ideal.mem_sup_left hw)
    refine e1.trans ((mem_some Q _ _ T w).trans ⟨?_, ?_⟩)
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (sFil Q r).S T := pow_tf Q c r (hT r) n T y (by
        have := sub_mem hw (hle T hy)
        rwa [sub_sub_cancel] at this)
      exact ⟨sqMk _ _ y hy', (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy')).2 hy⟩
    · rintro ⟨y, h⟩
      obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      exact ⟨y, (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy)).1 h⟩
  · intro T x hx
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e2 := (sqMk_eq_zero _ _ (c • w) (Submodule.smul_of_tower_mem _ _ hw)).1 hx
    exact (sqMk_eq_zero _ _ w hw).2 (hT _ T w e2)

end Gr

theorem lift_gr (hA : AfgA) {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ) (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) (hO : TFBase (dividedPowersBot O) l m)
    (hL : LatBase γ l m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < m) (j : ℕ) :
    ∃ k : ℕ, (∀ x : ∀ n, HGm (TS γ q l m {⊤}) ((l : A) ^ n) r j, (∀ n, trG (TS γ q l m {⊤}) (l : A) n r j (x (n + 1)) = x n) →
      ∃ z : HG (TS γ q l m {⊤}) r j, ∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = (l : A) ^ (2 * k) • x n) ∧
    ∀ z : HG (TS γ q l m {⊤}) r j, (∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = 0) → (l : A) ^ k • z = 0 := by
  have hf := fun j => hA γ l m m hdv hO hL le_rfl q U {⊤} sSup_singleton r ((r : ℤ) + 1) (by omega) (by omega) j
  obtain ⟨k, a, b, d⟩ := bounds hL (hf j) (hf (j + 1))
  refine ⟨k, gr_part (TS γ q l m {⊤}) (l : A) r ?_ j k a b d⟩
  intro r T x h
  have e : (l : A) • x = (l : T.obj.B) * (show T.obj.B from x) := by
    rw [Algebra.smul_def, map_natCast]
  rw [e] at h
  exact T.property.1.2 _ _ h

theorem sub_trans {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂}
    (m : GlobalTheory.LogCris.Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a))
    (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hs : Function.Surjective c₁) (r j : ℕ) (x : CH.H (B.pdS (nlFun δ₁ l X q κ₁) c₁ r).fn j) :
    (redSub q s 𝒱 d₂ c₂ lam hc₂ r).pull j ((pdOm m (RingHom.id Λ) h₀ r).pull j x) =
      trG (TS γ q l s 𝒱) (l : A) n r j ((redSub q s 𝒱 d₁ c₁ lam hc₁ r).pull j x) := by
  have hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x) := fun x => by
    obtain ⟨a, rfl⟩ := hs x
    rw [h₀, hc₁, hc₂]; rfl
  rw [pull_pull lam]
  change _ = (sqLe (stdI_le (TS γ q l s 𝒱) (some (r : ℤ)) (l : A) n) (stdI_le (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) (l : A) n)).pull j _
  rw [pull_pull lam]
  refine (CrystallineSemistableComparison.P.prism _ _ ⟨fun T => GlobalTheory.CompanionTheory.RedTrans.eta d₁ d₂ m hpt hρ T.obj T.property.1, fun T T' f => ?_⟩
    (fun T x => ?_) j x).symm
  · refine hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) x
    rfl

end CrystallineSemistableComparison.HT.RhoA
