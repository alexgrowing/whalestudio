import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
import Formalism.LocalToGlobal.CharacterGerms.RowTieProj

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePE0

open PartialDerivEval

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem actK_self (B : FB C dd O) (a : O) : B.actK C a = B.A.act a := by
  funext i; unfold FB.actK; rw [show algebraMap C C = RingHom.id C from rfl, map_id]; rfl

theorem TendsS.ev {m n : ℕ} {a : ℕ → Fin m → Pt C n dd} {A : Fin m → Pt C n dd} {f : ℕ → PS C m dd}
    {F : PS C m dd} (ha0 : ∀ k, Z0 (a k)) (hA0 : Z0 A) (ha : ∀ j i, TendsS V (fun k => a k j i) (A j i))
    (hf : TendsS V f F) : TendsS V (fun k => ev (a k) (f k)) (ev A F) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  exact TendsS.subst (fun k p => ha0 k p.1 p.2) (fun p => hA0 p.1 p.2) (fun p => ha p.1 p.2) hf

theorem constant_zero_two_points {n : ℕ} (P Q : Pt C n dd) (hP : ∀ i, constantCoeff (P i) = 0) (hQ : ∀ i, constantCoeff (Q i) = 0) :
    Z0 (![P, Q] : Fin 2 → Pt C n dd) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem tends_two {n : ℕ} {P Q : ℕ → Pt C n dd} {P' Q' : Pt C n dd} (hP : ∀ i, TendsS V (fun k => P k i) (P' i))
    (hQ : ∀ i, TendsS V (fun k => Q k i) (Q' i)) :
    ∀ j i, TendsS V (fun k => (![P k, Q k] : Fin 2 → Pt C n dd) j i) ((![P', Q'] : Fin 2 → Pt C n dd) j i) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem const_comp1 {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) {b : Pt C n dd}
    (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin dd) : constantCoeff (comp1 φ b i) = 0 :=
  const_ev (z0_1 b hb) (hφ i)

theorem TendsS.comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {Φ : Pt C 1 dd} {b : ℕ → Pt C n dd} {B : Pt C n dd}
    (hb0 : ∀ k i, constantCoeff (b k i) = 0) (hB0 : ∀ i, constantCoeff (B i) = 0)
    (hφ : ∀ i, TendsS V (fun k => φ k i) (Φ i)) (hb : ∀ i, TendsS V (fun k => b k i) (B i)) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) (b k) i) (comp1 Φ B i) :=
  TendsS.ev (fun k => z0_1 _ (hb0 k)) (z0_1 _ hB0)
    (fun j i' => by rw [Fin.fin_one_eq_zero j]; exact hb i') (hφ i)

theorem TendsS.expS {n : ℕ} {g : ℕ → PS C n dd} {G : PS C n dd} (hg0 : ∀ k, constantCoeff (g k) = 0)
    (hG0 : constantCoeff G = 0) (hg : TendsS V g G) : TendsS V (fun k => FB.expS C (g k)) (FB.expS C G) := by
  unfold FB.expS PowerSeries.subst
  exact TendsS.subst (fun k _ => hg0 k) (fun _ => hG0) (fun _ => hg) (TendsS.const _)

theorem exists_lim (Y : FBChart C V O dd) {φ : ℕ → Pt C 1 dd}
    (hφ : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (coeff μ (φ (n + 1) i) - coeff μ (φ n i))) :
    ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => φ n i) (e i) := by
  have h : ∀ i μ, ∃ x, Tends V (fun n => coeff μ (φ n i)) x := fun i μ => exists_tends Y.cpl fun N => hφ N i μ
  choose L hL using h
  exact ⟨fun i => (fun μ => L i μ : MvPowerSeries (Fin 1 × Fin dd) C), fun i μ => hL i μ⟩

theorem const_of_lim (Y : FBChart C V O dd) {a : ℕ → O} {e : Pt C 1 dd}
    (he : ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i)) (i : Fin dd) : constantCoeff (e i) = 0 := by
  have h := he i 0
  simp only [coeff_zero_eq_constantCoeff_apply, Y.B.A.const] at h
  exact h.unique (tends_const 0)

theorem endomorphism_limit_integral (Y : FBChart C V O dd) : EndomorphismLimitIntegral Y := by
  intro a ha hb
  obtain ⟨e, he⟩ := exists_lim Y (φ := fun n => Y.B.A.act (a n)) ha
  obtain ⟨eb, heb⟩ := exists_lim Y (φ := fun n => Y.B.A.act (star (a n))) hb
  have e0 := const_of_lim Y he
  have eb0 := const_of_lim Y (a := fun n => star (a n)) heb
  have act0 : ∀ x i, constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨e, eb, fun i => (he i).intS fun n => Y.intAct _ i, fun i => (heb i).intS fun n => Y.intAct _ i,
    fun N i μ => he i μ N, fun N i μ => heb i μ N, ?_, ?_⟩
  ·
    funext i
    have hP : ∀ i, constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) i) = 0 :=
      fun j => const_addOf Y 0 1 j
    have L := TendsS.comp1 (φ := fun k => Y.B.A.act (a k)) (b := fun _ => addOf Y.B.G.F (pt C (n := 2) dd 0)
      (pt C (n := 2) dd 1)) (fun _ => hP) hP he (fun j => TendsS.const _) i
    have hc : ∀ (j : Fin 2) k i', constantCoeff (comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd j) i') = 0 :=
      fun j k i' => const_comp1 (act0 _) (fun _ => z0_pt j _) i'
    have hcl : ∀ (j : Fin 2) i', constantCoeff (comp1 e (pt C (n := 2) dd j) i') = 0 :=
      fun j i' => const_comp1 e0 (fun _ => z0_pt j _) i'
    have R := TendsS.ev (V := V) (f := fun _ => Y.B.G.F i) (F := Y.B.G.F i)
      (a := fun k => ![comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 0), comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 1)])
      (A := ![comp1 e (pt C (n := 2) dd 0), comp1 e (pt C (n := 2) dd 1)])
      (fun k => constant_zero_two_points _ _ (hc 0 k) (hc 1 k)) (constant_zero_two_points _ _ (hcl 0) (hcl 1))
      (tends_two (TendsS.comp1 (fun _ => z0_pt 0) (z0_pt 0) he (fun _ => TendsS.const _))
        (TendsS.comp1 (fun _ => z0_pt 1) (z0_pt 1) he (fun _ => TendsS.const _))) (TendsS.const _)
    have eq : (fun k => comp1 (Y.B.A.act (a k)) (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) i) =
        fun k => ev ![comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 0), comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 1)]
          (Y.B.G.F i) := funext fun k => by rw [Y.B.A.hom (a k)]; rfl
    rw [eq] at L
    exact L.unique R
  ·
    let g : ℕ → PS C 2 dd := fun k => ev (n := 2) ![comp1 (Y.B.A.act (a k)) (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 (Y.B.A.act (star (a k))) (pt C dd 1)] Y.h
    have hc0 : ∀ k, Z0 (![comp1 (Y.B.A.act (a k)) (pt C dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) :=
      fun k => constant_zero_two_points _ _ (const_comp1 (act0 _) (fun _ => z0_pt 0 _)) (fun _ => z0_pt 1 _)
    have hc1 : ∀ k, Z0 (![pt C dd 0, comp1 (Y.B.A.act (star (a k))) (pt C dd 1)] : Fin 2 → Pt C 2 dd) :=
      fun k => constant_zero_two_points _ _ (fun _ => z0_pt 0 _) (const_comp1 (act0 _) (fun _ => z0_pt 1 _))
    have hC0 : Z0 (![comp1 e (pt C dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) :=
      constant_zero_two_points _ _ (const_comp1 e0 (fun _ => z0_pt 0 _)) (fun _ => z0_pt 1 _)
    have hC1 : Z0 (![pt C dd 0, comp1 eb (pt C dd 1)] : Fin 2 → Pt C 2 dd) :=
      constant_zero_two_points _ _ (fun _ => z0_pt 0 _) (const_comp1 eb0 (fun _ => z0_pt 1 _))
    have hg : TendsS V g (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h) :=
      (TendsS.ev hc0 hC0 (tends_two (TendsS.comp1 (fun _ => z0_pt 0) (z0_pt 0) he (fun _ => TendsS.const _))
        (fun _ => TendsS.const _)) (TendsS.const _)).sub
      (TendsS.ev hc1 hC1 (tends_two (fun _ => TendsS.const _)
        (TendsS.comp1 (fun _ => z0_pt 1) (z0_pt 1) heb (fun _ => TendsS.const _))) (TendsS.const _))
    have hh := h_const Y
    have hg0 : ∀ k, constantCoeff (g k) = 0 := fun k => by
      simp only [g, map_sub, constantCoeff_ev (hc0 k), constantCoeff_ev (hc1 k), hh, sub_zero]
    have hG0 : constantCoeff (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h) = 0 := by
      simp only [map_sub, constantCoeff_ev hC0, constantCoeff_ev hC1, hh, sub_zero]
    have hE := TendsS.expS hg0 hG0 hg
    have hadk : ∀ k, FB.expS C (g k) = Y.B.ad (a k) := fun k => by
      have h1 := Y.gauge.ad (a k)
      rw [toK_self, actK_self, actK_self] at h1
      exact h1.symm
    simp only [hadk] at hE
    exact hE.intS fun k => Y.intAd _

theorem endomorphism_limit_all : EndomorphismLimitAll := fun _ _ _ _ _ _ _ _ Y => endomorphism_limit_integral Y

end RowTiePE0

end Formalism.L2.FormalSeriesBounds
