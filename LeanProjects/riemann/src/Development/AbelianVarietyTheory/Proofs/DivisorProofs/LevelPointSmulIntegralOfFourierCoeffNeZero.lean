import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HatInt

noncomputable section

theorem omegaK_congr {D : D7} {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  refine if_congr (forall₂_congr fun PP hP => ?_) rfl rfl
  rw [h PP hP]

theorem omegaQ_congr {D : D7} {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Q, y PP = y' PP) : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
  unfold omegaQ
  refine dite_congr (propext (forall₂_congr fun PP hP => by rw [h PP hP])) (fun h1 => ?_) (fun _ => rfl)
  refine Finset.prod_congr rfl fun PP _ => ?_
  congr 3
  apply Units.ext
  simp only [IsUnit.unit_spec]
  rw [h PP.1 PP.2]

theorem matrix_map_ringHom_add_smul_sandwich {K S : Type} [CommRing K] [CommRing S] (f : K →+* S) {m n : Type} [Fintype m] [Fintype n]
    (B : Matrix m m S) (C : Matrix n n S) (P : Matrix m m K) (Q : Matrix n n K) (X Y : Matrix m n K) (d : K) :
    B * (P * (X + d • Y) * Q).map f * C = B * (P * X * Q).map f * C + f d • (B * (P * Y * Q).map f * C) := by
  have h2 : ∀ (P Q : Matrix m n K), (P + d • Q).map f = P.map f + f d • Q.map f := by
    intro P Q; ext b a; simp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h2]

theorem uMat_add_smul {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X Y : Fin S.rank → Fin T.rank → D.host.E) (c : D.host.E) :
    FWT.uMat S T βS βT e (fun b => X b + c • Y b) =
      fun b a => FWT.uMat S T βS βT e X b a + eToEAf D (D.sp.cm.sig c) * FWT.uMat S T βS βT e Y b a := by
  have h1 : (Matrix.of fun b a => D.sp.cm.sig ((X b + c • Y b) a)) =
      (Matrix.of fun b a => D.sp.cm.sig (X b a)) + D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a; simp
  funext b a
  have h2 := congrFun (congrFun (matrix_map_ringHom_add_smul_sandwich (eToEAf D) (βS⁻¹).val βT.val S.gram⁻¹ T.gram
    (Matrix.of fun b a => D.sp.cm.sig (X b a)) (Matrix.of fun b a => D.sp.cm.sig (Y b a)) (D.sp.cm.sig c)) b) a
  rw [← h1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h2
  have h3 := congrArg (fun u => toEAf D e * u) h2
  simp only [mul_add] at h3
  rw [mul_left_comm] at h3
  exact h3

theorem subring_reduction_add_mul_killed {S k : Type} [CommRing S] [CommRing k] (O : Subring S) (f : O →+* k) (x y : S) (hx : x ∈ O) (hy : y ∈ O)
    (c : O) (hc : f c = 0) :
    (if h : x + (c : S) * y ∈ O then f ⟨x + (c : S) * y, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hmem : x + (c : S) * y ∈ O := add_mem hx (mul_mem c.2 hy)
  rw [dif_pos hmem, dif_pos hx]
  have : (⟨_, hmem⟩ : O) = ⟨x, hx⟩ + c * ⟨y, hy⟩ := rfl
  rw [this, map_add, map_mul, hc, zero_mul, add_zero]

theorem redM_add_smul {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N N' : Matrix (Fin b) (Fin a) (EAf D))
    (hN : Datum.IsIntM N) (hN' : Datum.IsIntM N') (s : 𝓞 D.host.E) (hs : s ∈ PP.asIdeal) :
    Datum.redM PP (fun i j => N i j + eToEAf D (s : D.host.E) * N' i j) = Datum.redM PP N := by
  funext i j
  have h0 : ((Formalism.L2.DIV.oToS D.host.F D.host.E s : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      eToEAf D (s : D.host.E) := by
    unfold Formalism.L2.DIV.oToS eToEAf
    rw [RingHom.codRestrict_apply]
    rfl
  rw [← h0]
  unfold Datum.redM
  exact subring_reduction_add_mul_killed _ (Formalism.L2.DIV.resS D.host.F PP) _ _ (hN i j) (hN' i j) _
    (by rw [Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hs])

theorem sig_bar {D : D7} (H : Geo.Tor.Host D.host.E) (s : 𝓞 D.host.E) :
    D.sp.cm.sig ((H.bar s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
  rw [H.bar_eq]
  exact IsCMField.complexConj_apply_apply D.host.E (s : D.host.E)

theorem dvd_of_invariant {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    (l : Geo.Tor.Level H) {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) (hq : hatC l φ q ≠ 0)
    (z : Fin n → Dw.La) (hφ : ∀ x, φ (x + fun b => Submodule.Quotient.mk (z b)) = φ x) :
    (l.M : ℤ) ∣ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hp := Complex.isPrimitiveRoot_exp l.M hM
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) with hζ
  have h0 : ζ ≠ 0 := hp.ne_zero hM
  have hrep : ∀ y : LevQc Dw l, Submodule.Quotient.mk (qRep y) = y := fun y =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ y)
  have key : hatC l φ q = ζ ^ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) * hatC l φ q := by
    unfold hatC
    rw [mul_finsum, ← finsum_comp_equiv (Equiv.addRight (fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)))]
    refine finsum_congr fun x => ?_
    simp only [Equiv.coe_addRight]
    rw [hφ, mul_left_comm, ← zpow_add₀ h0]
    congr 1
    have hd := LevelPairing.pairL_congr (l := l)
      (fun b => qRep ((x + fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)) b)) (fun b => z b + qRep (x b))
      (fun b => levRep (q b)) (fun b => levRep (q b))
      (fun b => (Submodule.Quotient.eq _).1 (by
        rw [hrep, Submodule.Quotient.mk_add, hrep, add_comm]; rfl)) (fun b => by simp)
    have ha : Formalism.L2.Pj.pairL (l := l) (fun b => z b + qRep (x b)) (fun b => levRep (q b)) =
        Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) +
          Formalism.L2.Pj.pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)) := by
      simp [Formalism.L2.Pj.pairL, Finset.sum_add_distrib]
    rw [← ha]
    have := (hp.zpow_eq_one_iff_dvd _).2 hd
    rwa [zpow_sub₀ h0, div_eq_one_iff_eq (zpow_ne_zero _ h0)] at this
  rw [← hp.zpow_eq_one_iff_dvd]
  exact (mul_left_eq_self₀.1 key.symm).resolve_right hq

theorem smul_eq_of_hatC_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    have h1 := dvd_of_invariant l₂ φ q hq (fun b' => H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b') (by
      intro x
      obtain ⟨x, rfl⟩ : ∃ x' : Fin (Vc D i).rank → Dw.La, x = fun b => Submodule.Quotient.mk (x' b) :=
        ⟨fun b => qRep (x b), funext fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm⟩
      have e1 := (he (fun b' => x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')).2
      have e2 := (he x).2
      simp only [RingHom.id_apply] at e1 e2
      have e3 : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b' => ι (x b')) := by
        intro PP hP
        have e4 : (fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
            fun b' => ι (x b') + ((H.bar s : 𝓞 D.host.E) : D.host.E) •
              ι ((Pi.single b w : Fin (Vc D i).rank → Dw.La) b') := by
          funext b'
          rw [map_add, map_smul]
          rfl
        rw [e4, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he x).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => e3 PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => e3 PP (Or.inr hP)), ← e2] at e1
      exact e1)
    unfold Formalism.L2.Pj.pairL at h1
    rw [Finset.sum_eq_single b] at h1
    · simpa [Dw.adj, LevelPairing.bar_bar] using h1
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have h2 := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add, LinearMap.add_apply, Dw.alt, zero_add, add_zero] at h2
    have h3 := hdvd y
    have : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by linarith
    rw [this]; exact h3.neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩

end

end GlobalTheory.HatInt
