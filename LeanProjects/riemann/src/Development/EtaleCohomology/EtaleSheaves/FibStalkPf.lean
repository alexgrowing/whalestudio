import Development.EtaleCohomology.EtaleSheaves.FibClosedPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf

namespace LateralTheory.E.FibStalkPf

theorem eqv_iso {X Y : Scheme.{0}} (e : X ≅ Y) (q : ℕ) (i : ℤ) : Eqv _ (sch.map e.hom) (tw q i) := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (sch.map e.inv) (tw q i) n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_comp {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (hf : Eqv _ f F) (hg : Eqv _ g F) :
    Eqv _ (f ≫ g) F := by
  intro n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_left {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hg : Eqv _ g F) :
    Eqv _ f F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff _ (hg n)).1 h1

theorem eqv_right {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hf : Eqv _ f F) :
    Eqv _ g F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 h1

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSH : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of A)),
  AICSch S → ∀ s : (pullback p (cpt A) : Scheme.{0}), SH ((pullback p (cpt A)).presheaf.stalk s)

def FibreEqv : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.snd (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))
      (cpt ((pullback p (cpt A)).presheaf.stalk s)))) (tw q i)

theorem FibStalk_of (hS : StalkSH) (hF : FibreEqv) : FibStalk := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  have hsh : SH ((pullback p (cpt A)).presheaf.stalk s) := hS A p hSs s
  obtain ⟨_, _⟩ := id hsh
  have hu0 : IsUnit (q : Γ((pullback p (cpt A) : Scheme.{0}), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  have hu : IsUnit (q : (pullback p (cpt A)).presheaf.stalk s) := by
    simpa using hu0.map ((pullback p (cpt A)).presheaf.germ ⊤ s trivial).hom
  have hfst := hB _ hsh hu ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A))
  have hfib := hF H h0 hA q i A hq c p hZs hSs hB s
  have hE1 : Eqv _ (sch.map (cpt ((pullback p (cpt A)).presheaf.stalk s))) (tw q i) :=
    H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  have core : Eqv _ (sch.map (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))) (tw q i) := by
    refine eqv_right ?_ hfst
    rw [← Functor.map_comp, pullback.condition, Functor.map_comp]
    exact eqv_comp hfib hE1
  have sq2 : IsPullback (pullback.fst (c ≫ p) (cpt A)) (fm c p ≫ 𝟙 _) c (pullback.fst p (cpt A)) := by
    rw [Category.comp_id]; exact (fm_isPullback c p).flip
  have big := (IsPullback.of_hasPullback (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s)).paste_horiz sq2
  have hsnd : Eqv _ (sch.map (pullback.snd (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) (tw q i) := by
    rw [← big.isoPullback_hom_snd, Functor.map_comp]; exact eqv_comp (eqv_iso _ q i) core
  refine eqv_left (g := sch.map (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) ?_
    (eqv_iso (asIso (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) q i)
  rw [← Functor.map_comp]
  convert hsnd using 2
  rw [pullback.map]; erw [pullback.lift_snd]; exact Category.comp_id _

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSHS : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, SH (S.presheaf.stalk x)

def QuotSH : Prop := ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R'), Function.Surjective f → SH R → SH R'

theorem StalkSH_of (hS : StalkSHS) (hQ : QuotSH) : StalkSH := by
  intro A _ _ S p hSs s
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks (pullback.fst p (cpt A)) := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  exact hQ _ _ ((pullback.fst p (cpt A)).stalkMap s).hom ((pullback.fst p (cpt A)).stalkMap_surjective s) (hS S hSs _)

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

theorem quotSH : QuotSH := by
  intro R R' _ _ _ f hf ⟨hH, hK⟩
  have hl : IsLocalHom f := IsLocalHom.of_surjective f hf
  have hmem : ∀ x, f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h hx => h (hx.map f), fun h hx => h (isUnit_of_map_unit f x hx)⟩
  refine ⟨⟨fun g hg a₀' h0 h1 => ?_⟩, ?_⟩
  · obtain ⟨G, hGm, -, hGmon⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts g).2 fun n => hf _) hg
    obtain ⟨a₀, rfl⟩ := hf a₀'
    have e0 : f (G.eval a₀) = g.eval (f a₀) := by rw [← hGm, Polynomial.eval_map, eval₂_at_apply]
    have e1 : f (G.derivative.eval a₀) = g.derivative.eval (f a₀) := by
      rw [← hGm, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian G hGmon a₀ ((hmem _).1 (e0 ▸ h0))
      (isUnit_of_map_unit f _ (e1 ▸ h1))
    refine ⟨f a, ?_, ?_⟩
    · rw [IsRoot, ← hGm, Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
    · rw [← map_sub]; exact (hmem _).2 ha'
  · have hs : Function.Surjective (ResidueField.map f) := by
      intro y
      obtain ⟨y, rfl⟩ := residue_surjective y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨residue R x, ResidueField.map_residue f x⟩
    refine IsSepClosed.of_exists_root _ fun p hpm hpi hps => ?_
    obtain ⟨P, hP, hdeg, -⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts p).2 fun n => hs _) hpm
    have hPs : P.Separable := (separable_map (ResidueField.map f)).1 (hP ▸ hps)
    have hPd : P.degree ≠ 0 := by
      have := hpi.natDegree_pos
      intro h; rw [natDegree_eq_zero_iff_degree_le_zero.2 h.le] at hdeg; omega
    obtain ⟨x, hx⟩ := IsSepClosed.exists_root P hPd hPs
    exact ⟨ResidueField.map f x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx.eq_zero]; simp⟩

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

theorem aic_root {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : ∀ (n : ℕ) (f : R[X]), f.Monic → f.natDegree = n →
    ∀ a₀, f.eval a₀ ∈ maximalIdeal R → ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hm hd a₀ h0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hm hd, eval_one] at h0
    exact absurd ((Ideal.eq_top_iff_one _).2 h0) (maximalIdeal.isMaximal R).ne_top
  | succ n ih =>
    intro f hm hd a₀ h0
    obtain ⟨b, hb⟩ := h f hm (by omega)
    have hf : (X - C b) * (f /ₘ (X - C b)) = f := by rw [mul_divByMonic_eq_iff_isRoot]; exact hb
    have hgm : (f /ₘ (X - C b)).Monic := (monic_X_sub_C b).of_mul_monic_left (by rw [hf]; exact hm)
    have hgd : (f /ₘ (X - C b)).natDegree = n := by rw [natDegree_divByMonic f (monic_X_sub_C b), natDegree_X_sub_C]; omega
    rw [← hf, eval_mul, eval_sub, eval_X, eval_C] at h0
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h0 with h1 | h2
    · exact ⟨b, hb, by rw [← neg_sub]; exact neg_mem h1⟩
    · obtain ⟨a, ha, ha'⟩ := ih _ hgm hgd a₀ h2
      exact ⟨a, by rw [IsRoot, ← hf, eval_mul, ha.eq_zero, mul_zero], ha'⟩

theorem sh_of_aic {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : SH R := by
  refine ⟨{ is_henselian := fun f hf a₀ h0 _ => aic_root h _ f hf rfl a₀ h0 }, ?_⟩
  refine IsSepClosed.of_exists_root _ fun p hpm hpi _ => ?_
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts p).2 fun n => residue_surjective _) hpm
  obtain ⟨x, hx⟩ := h P hPm (by have := hpi.natDegree_pos; omega)
  exact ⟨residue R x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx]; simp⟩

theorem stalkSHS_of (hA : StalkAIC) : StalkSHS := fun S hS x => sh_of_aic (hA S hS x)

end LateralTheory.E.FibStalkPf
