import Development.EtaleCohomology.EtaleSheaves.StalkGerm

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.ZarIndPf

def Bij (q : ℕ) (i n : ℤ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : Prop :=
  Function.Bijective (pull _ (sch.map (fO f p U)) (tw q i) n)

def InjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)

def SurjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Surjective (pull _ (sch.map (fO f p U)) (tw q i) n)

def Step : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U

theorem Step_of (h1 : InjStep) (h2 : SurjStep) : Step := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  exact ⟨h1 hM hH q f p hq i n hg hb U hU, h2 hM hH q f p hq i n hg hb (h1 hM hH q f p hq i n hg hb) U hU⟩

theorem pull_bij_of_iso {E E' : Spc} (g : E ⟶ E') [IsIso g] {q' : ℕ} (F : Shv (ZMod q')) (n : ℤ) :
    Function.Bijective (pull _ g F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (inv g) F n, fun x => ?_, fun x => ?_⟩
  · simp [← pull_comp, pull_id]
  · simp [← pull_comp, pull_id]

theorem bij_top {q : ℕ} {i n : ℤ} {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsIso (⊤ : S.Opens).ι] (h : Bij q i n f p ⊤) :
    Function.Bijective (pull _ (sch.map f) (tw q i) n) := by
  have e : fO f p ⊤ ≫ pullback.fst p (⊤ : S.Opens).ι = pullback.fst (f ≫ p) (⊤ : S.Opens).ι ≫ f := by
    exact pullback.lift_fst _ _ _
  have e2 : ∀ x, pull _ (sch.map (fO f p ⊤)) (tw q i) n (pull _ (sch.map (pullback.fst p (⊤ : S.Opens).ι)) _ n x) =
      pull _ (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) _ n (pull _ (sch.map f) _ n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, e]
  have b1 := pull_bij_of_iso (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n
  have b2 := pull_bij_of_iso (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n
  have hc : Function.Bijective ((pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n)) := by
    have : (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n) =
        (pull (ZMod q) (sch.map (fO f p ⊤)) (tw q i) n) ∘ (pull (ZMod q) (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n) :=
      funext fun x => (e2 x).symm
    rw [this]; exact h.comp b1
  refine ⟨hc.1.of_comp, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hc.2 (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n y)
  exact ⟨x, b2.1 hx⟩

theorem bij_neg (hH : Hyp) {q : ℕ} {i n : ℤ} (hn : n < 0) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    Bij q i n f p U := by
  have h1 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO p U)) n hn
  have h2 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO (f ≫ p) U)) n hn
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem ZarInd_of_step (hS : Step) : ZarInd := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i hg
  have P : ∀ n : ℤ, ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U := by
    intro n
    rcases lt_or_ge n 0 with hn | hn
    · exact fun U _ => bij_neg hH hn f p U
    induction n, hn using Int.le_induction with
    | base => exact hS hM hH q f p hq i 0 (fun s => hg s 0) (fun U _ => bij_neg hH (by norm_num) f p U)
    | succ m _ ih =>
      exact hS hM hH q f p hq i (m + 1) (fun s => hg s (m + 1)) (by simpa using ih)
  intro n
  have : IsIso (⊤ : S.Opens).ι := (Scheme.topIso S).isIso_hom
  exact bij_top f p (P n ⊤ (by simpa using isCompact_univ))

end LateralTheory.E.ZarIndPf
