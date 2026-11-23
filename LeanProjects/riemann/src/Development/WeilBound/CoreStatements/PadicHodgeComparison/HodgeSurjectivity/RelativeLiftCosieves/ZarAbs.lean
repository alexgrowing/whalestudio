import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

section General

universe w u v

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

theorem resU_pull_self {P : ObjectProperty C} (h : P ≤ P) (n : ℕ) (x : HU F P n) : (resU F h).pull n x = x := by
  rw [CrystallineSemistableComparison.P.prism (resU F h) (CH.Mor.id (P.ι ⋙ F)) { app := fun T => 𝟙 _ } (fun T y => by
    simp [resU, CH.Mor.id]) n x]
  exact (CrystallineSemistableComparison.P.pull_comp (CH.Mor.id (P.ι ⋙ F)) (CH.Mor.id (P.ι ⋙ F)) n x).2

theorem resU_pull_trans {P₁ P₂ P₃ : ObjectProperty C} (h₁₂ : P₂ ≤ P₁) (h₂₃ : P₃ ≤ P₂) (h₁₃ : P₃ ≤ P₁) (n : ℕ)
    (x : HU F P₁ n) : (resU F h₁₃).pull n x = (resU F h₂₃).pull n ((resU F h₁₂).pull n x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (resU F h₁₂) (resU F h₂₃) n x).1]
  exact CrystallineSemistableComparison.P.prism (resU F h₁₃) ((resU F h₁₂).comp (resU F h₂₃)) { app := fun T => 𝟙 _ } (fun T y => by
    simp [resU, CH.Mor.comp]) n x

theorem resU_bij_of_le {P P' : ObjectProperty C} (h : P' ≤ P) (h' : P ≤ P') (n : ℕ) :
    Function.Bijective ((resU F h).pull n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨(resU F h').pull n, fun x => ?_, fun x => ?_⟩
  · rw [← resU_pull_trans F h h' le_rfl, resU_pull_self]
  · rw [← resU_pull_trans F h' h le_rfl, resU_pull_self]

end General

variable {K : Type} [CommRing K] {Z : Scheme.{0}}

theorem sq_pull_eq_resU (q : Z ⟶ Spec (CommRingCat.of K)) {Q Q' : ObjectProperty (Thick (smFun Z q))} (h : Q' ≤ Q)
    (a n : ℕ) (x : HU (G q a) Q n) :
    ((incl h).sq (incl_fil h (a : ℤ)) (incl_fil h ((a : ℤ) + 1))).pull n x = (resU (G q a) h).pull n x := by
  let m0 := (incl h).sq (incl_fil h (a : ℤ)) (incl_fil h ((a : ℤ) + 1))
  let m : CH.Mor (Q.ι ⋙ G q a) (Q'.ι ⋙ G q a) (RingHom.id K) := m0
  refine CrystallineSemistableComparison.P.prism m (resU (G q a) h) (𝟙 _) (fun T y => ?_) n x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp only [resU, NatTrans.id_app]
  rfl

theorem bij_resU_of_sq (q : Z ⟶ Spec (CommRingCat.of K)) {Q Q' : ObjectProperty (Thick (smFun Z q))} (h : Q' ≤ Q)
    (a n : ℕ) (hb : Function.Bijective (((incl h).sq (incl_fil h (a : ℤ)) (incl_fil h ((a : ℤ) + 1))).pull n)) :
    Function.Bijective ((resU (G q a) h).pull n) := by
  refine ⟨fun x y hxy => hb.1 ?_, fun y => ?_⟩
  · rw [sq_pull_eq_resU q h a n x, sq_pull_eq_resU q h a n y]
    exact hxy
  · obtain ⟨x, hx⟩ := hb.2 y
    exact ⟨x, (sq_pull_eq_resU q h a n x).symm.trans hx⟩

abbrev StT (q : Z ⟶ Spec (CommRingCat.of K)) (s : ℕ) (𝒱 : Set Z.Opens) : ObjectProperty (Thick (smFun Z q)) :=
  St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) 𝒱

abbrev StA (q : Z ⟶ Spec (CommRingCat.of K)) (𝒱 : Set Z.Opens) : ObjectProperty (Thick (smFun Z q)) :=
  St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 𝒱

theorem stT_le_stA (q : Z ⟶ Spec (CommRingCat.of K)) (s : ℕ) (𝒱 : Set Z.Opens) : StT q s 𝒱 ≤ StA q 𝒱 :=
  fun _ hT => ⟨trivial, hT.2⟩

theorem bij_trunc (q : Z ⟶ Spec (CommRingCat.of K)) (a n : ℕ) (𝒱 : Set Z.Opens) :
    Function.Bijective ((resU (G q a) (stT_le_stA q (a + 1) 𝒱)).pull n) :=
  bij_resU_of_sq q _ a n (Pb.refl ⊤ 1 (a + 1) (Or.inl ⟨rfl, rfl⟩) 𝒱 (stT_le_stA q (a + 1) 𝒱) (a : ℤ) ((a : ℤ) + 1)
    (by push_cast; exact le_rfl) n)

theorem inU_le_stA (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : inU q V ≤ StA q {V} :=
  fun _ hT => ⟨trivial, V, rfl, hT⟩

theorem stA_le_inU (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : StA q {V} ≤ inU q V := by
  rintro T ⟨-, W, hW, hT⟩
  rw [Set.mem_singleton_iff] at hW
  subst hW
  exact hT

theorem cov_le_stA (q : Z ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → Z.Opens) :
    (fun T => ∃ α, inU q (U α) T) ≤ StA q (Set.range U) :=
  fun _ ⟨α, hT⟩ => ⟨trivial, U α, ⟨α, rfl⟩, hT⟩

theorem stA_le_cov (q : Z ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → Z.Opens) :
    StA q (Set.range U) ≤ fun T => ∃ α, inU q (U α) T := by
  rintro T ⟨-, W, ⟨α, rfl⟩, hT⟩
  exact ⟨α, hT⟩

theorem zarAbs_pf : ZarAbs := by
  intro K _ Z q ι V U hU h a n

  have hTU : StT q (a + 1) (Set.range U) ≤ StT q (a + 1) {V} := by
    rintro T ⟨hT, W, ⟨α, rfl⟩, hW⟩
    exact ⟨hT, V, rfl, h T ⟨α, hW⟩⟩
  have hc : ∀ W ∈ ({V} : Set Z.Opens), W ≤ sSup (Set.range U) := by
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    rw [← hU, sSup_range]

  have hZ : Function.Bijective ((resU (G q a) hTU).pull n) :=
    bij_resU_of_sq q hTU a n ((Pb.zar (TF 1 (a + 1)) (Or.inl ⟨rfl, 1, a + 1, rfl⟩) (Set.range U) {V} hTU hc n).1
      (a : ℤ) ((a : ℤ) + 1))

  have hPV : (StT q (a + 1) {V}) ≤ inU q V := (stT_le_stA q (a + 1) {V}).trans (stA_le_inU q V)
  have hPVb : Function.Bijective ((resU (G q a) hPV).pull n) := by
    have e : ∀ x, (resU (G q a) hPV).pull n x =
        (resU (G q a) (stT_le_stA q (a + 1) {V})).pull n ((resU (G q a) (stA_le_inU q V)).pull n x) :=
      resU_pull_trans (G q a) _ _ _ n
    have hb := (bij_trunc q a n {V}).comp (resU_bij_of_le (G q a) (stA_le_inU q V) (inU_le_stA q V) n)
    exact (funext e : ⇑((resU (G q a) hPV).pull n) = _) ▸ hb

  have hPU : (StT q (a + 1) (Set.range U)) ≤ fun T => ∃ α, inU q (U α) T :=
    (stT_le_stA q (a + 1) (Set.range U)).trans (stA_le_cov q U)
  have hPUb : Function.Bijective ((resU (G q a) hPU).pull n) := by
    have e : ∀ x, (resU (G q a) hPU).pull n x =
        (resU (G q a) (stT_le_stA q (a + 1) (Set.range U))).pull n ((resU (G q a) (stA_le_cov q U)).pull n x) :=
      resU_pull_trans (G q a) _ _ _ n
    have hb := (bij_trunc q a n (Set.range U)).comp (resU_bij_of_le (G q a) (stA_le_cov q U) (cov_le_stA q U) n)
    exact (funext e : ⇑((resU (G q a) hPU).pull n) = _) ▸ hb

  have hsq : ⇑((resU (G q a) hPU).pull n) ∘ ⇑((resU (G q a) h).pull n) =
      ⇑((resU (G q a) hTU).pull n) ∘ ⇑((resU (G q a) hPV).pull n) := by
    funext x
    simp only [Function.comp_apply]
    rw [← resU_pull_trans (G q a) h hPU (hTU.trans hPV), ← resU_pull_trans (G q a) hPV hTU (hTU.trans hPV)]
  have hcomp : Function.Bijective (⇑((resU (G q a) hPU).pull n) ∘ ⇑((resU (G q a) h).pull n)) := by
    rw [hsq]
    exact hZ.comp hPVb
  exact (Function.Bijective.of_comp_iff' hPUb _).1 hcomp

end CrystallineSemistableComparison.Onto

end
