import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterPrincipalSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.Comparison₂

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem vEq (w : Pl D.host.E) :
    (valuation (Kw w)).IsEquiv (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem cpt_tmul (w : Pl D.host.E) (x : D.host.E) :
    cpt (D := D) w (x ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) = algebraMap D.host.E (Kw w) x :=
  congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) x)

theorem v_oToS_le (w : Pl D.host.E) (a : 𝓞 D.host.E) (e : ℕ) :
    Valued.v (cpt (D := D) w (oToS D.host.F D.host.E a).1) ≤ WithZero.exp (-(e : ℤ)) ↔ a ∈ w.asIdeal ^ e := by
  rw [oToS_coe, cpt_tmul, ← w.intValuation_le_pow_iff_mem, ← w.valuation_of_algebraMap (K := D.host.E),
    Formalism.UG.P.levelaf_valued_algebraMap]

theorem v_le_of_mem_idS {w : Pl D.host.E} {e : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≤ w.asIdeal ^ e) {s : OA D}
    (hs : s ∈ idS D.host.F 𝔪) : Valued.v (cpt (D := D) w s.1) ≤ WithZero.exp (-(e : ℤ)) := by
  refine Submodule.span_induction (p := fun s _ => Valued.v (cpt (D := D) w (s : OA D).1) ≤ WithZero.exp (-(e : ℤ)))
    ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact (v_oToS_le w a e).2 (h ha)
  · simp
  · intro x y _ _ hx hy
    rw [Subring.coe_add, RingHom.map_add]
    exact Valuation.map_add_le _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, RingHom.map_mul, Valuation.map_mul]
    exact mul_le_of_le_one_of_le ((mem_OA_iff _).1 c.2 w) hx

theorem exists_approx {𝔪 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≠ ⊥) (s : OA D) :
    ∃ a, s - oToS D.host.F D.host.E a ∈ idS D.host.F 𝔪 := by
  obtain ⟨q, hq⟩ := cmpS_surj (F := D.host.F) 𝔪 h (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨a, Ideal.Quotient.eq.1 hq.symm⟩

theorem mem_idS_of_v_le {ι : Type} {S : Finset ι} {w : ι → Pl D.host.E} {e : ι → ℕ} {𝔪 : Ideal (𝓞 D.host.E)} (h0 : 𝔪 ≠ ⊥)
    (h : 𝔪 = S.inf fun i => (w i).asIdeal ^ e i) {s : OA D}
    (hs : ∀ i ∈ S, Valued.v (cpt (D := D) (w i) s.1) ≤ WithZero.exp (-(e i : ℤ))) : s ∈ idS D.host.F 𝔪 := by
  obtain ⟨a, ha⟩ := exists_approx h0 s
  have h1 : a ∈ 𝔪 := h ▸ Submodule.mem_finsetInf.2 fun i hi => (v_oToS_le _ a _).1 (by
    have h2 := v_le_of_mem_idS (h.le.trans (Finset.inf_le hi)) ha
    rw [AddSubgroupClass.coe_sub, RingHom.map_sub] at h2
    simpa using Valuation.map_sub_le _ (hs i hi) h2)
  simpa using add_mem ha (Ideal.mem_map_of_mem (oToS D.host.F D.host.E) h1)

theorem mem_idS_modul (G : GridData L sc) (s : OA D) : s ∈ idS D.host.F G.modul ↔
    ∀ w ∈ G.pl.W0, Valued.v (cpt (D := D) w s.1) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  classical
  have h : G.modul = G.pl.S0.inf fun v => (G.pl.w v).asIdeal ^ G.pl.depth sc v :=
    (HeightOneSpectrum.inf_pow_eq_prod _ _ _ fun v hv v' hv' hne h =>
      hne ((G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv')))).symm
  have hW : ∀ w, w ∈ G.pl.W0 ↔ ∃ v ∈ G.pl.S0, G.pl.w v = w := fun w => by unfold Places.W0; convert Finset.mem_image
  refine ⟨fun hs w hw => ?_, fun hs => mem_idS_of_v_le (G.pl.modul_ne_bot sc) h fun v hv => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := (hW w).1 hw
    rw [(depthAt_w G hv).1]
    exact v_le_of_mem_idS (h.le.trans (Finset.inf_le hv)) hs
  · rw [← (depthAt_w G hv).1]
    exact hs _ ((hW _).2 ⟨v, hv, rfl⟩)

theorem mem_matLat_pow (w : Pl D.host.E) (e : ℕ) {a b : ℕ} (X : Matrix (Fin a) (Fin b) (Kw w)) :
    X ∈ matLat _ (unifAt w ^ e • stdLat (Kw w) _) ↔ ∀ i j, Valued.v (X i j) ≤ WithZero.exp (-(e : ℤ)) := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [mem_matLat, SplitFlip.stdLat, smul_diagLat]
  refine forall₂_congr fun i j => (vEq w _ _).trans ?_
  change Valued.v (X i j) ≤ Valued.v ((unifAt w ^ e * 1 : (Kw w)ˣ) : Kw w) ↔ _
  rw [mul_one, Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

abbrev fr {A : Type} [CommRing A] {m n : ℕ} (β' : GL (Fin m) A) (β : GL (Fin n) A) (x : Matrix (Fin m) (Fin n) A) :
    Matrix (Fin m) (Fin n) A := (β'⁻¹).val * x * β.val

theorem coord_map {G : GridData L sc} (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ}
    (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m) (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (x : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (EAf D)) :
    B.coord t w hX hY (x.map (cpt (D := D) w)) = (((fr (B.β X.1 X.2) (B.β Y.1 Y.2) x).map (cpt (D := D) w)).submatrix
      (Fin.cast (rank_vertex G t w hX)) (Fin.cast (rank_vertex G t w hY)))ᵀ := by
  rw [Frames.coord, Matrix.map_mul, Matrix.map_mul, ← map_inv]
  rfl

theorem fr_add {A : Type} [CommRing A] {m n : ℕ} (β' : GL (Fin m) A) (β : GL (Fin n) A) (x y : Matrix (Fin m) (Fin n) A) :
    fr β' β (x + y) = fr β' β x + fr β' β y := by rw [fr, Matrix.mul_add, Matrix.add_mul]

theorem fr_sub {A : Type} [CommRing A] {m n : ℕ} (β' : GL (Fin m) A) (β : GL (Fin n) A) (x y : Matrix (Fin m) (Fin n) A) :
    fr β' β (x - y) = fr β' β x - fr β' β y := by rw [fr, Matrix.mul_sub, Matrix.sub_mul]

theorem fr_smul {A : Type} [CommRing A] {m n : ℕ} (β' : GL (Fin m) A) (β : GL (Fin n) A) (c : A)
    (x : Matrix (Fin m) (Fin n) A) : fr β' β (c • x) = c • fr β' β x := by rw [fr, Matrix.mul_smul, Matrix.smul_mul]

theorem fr_sub_map {A E : Type} [CommRing A] [CommRing E] {m n : ℕ} (β' : GL (Fin m) A) (β : GL (Fin n) A) (f : E →+* A)
    (x : Matrix (Fin m) (Fin n) A) (y y' : Matrix (Fin m) (Fin n) E) (i : Fin m) (j : Fin n) :
    fr β' β (x - y.map f) i j = fr β' β (x - y'.map f) i j + fr β' β ((y' - y).map f) i j := by
  rw [← Matrix.add_apply, ← fr_add, Matrix.map_sub _ f.map_sub, sub_add_sub_cancel]

theorem hom_sum {A B ι : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s

theorem v_mul_add_le {w : Pl D.host.E} {z e a b : EAf D} {c : WithZero (Multiplicative ℤ)} (h : z = e * (a + b))
    (he : cpt (D := D) w e = 1) (ha : Valued.v (cpt (D := D) w a) ≤ c) (hb : Valued.v (cpt (D := D) w b) ≤ c) :
    Valued.v (cpt (D := D) w z) ≤ c := by
  rw [h, RingHom.map_mul, he, one_mul, RingHom.map_add]
  exact Valuation.map_add_le _ ha hb

theorem cpt_mul_mem {w : Pl D.host.E} {z e a : EAf D} (h : z = e * a) (he : cpt (D := D) w e = 0) :
    cpt (D := D) w z ∈ w.adicCompletionIntegers D.host.E := by
  rw [h, RingHom.map_mul, he, zero_mul]
  exact zero_mem _

section Cosets

variable {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
  {β : GL (Fin n) (EAf D)} {β' : GL (Fin m) (EAf D)}

theorem mem_hatMx_iff (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ') (𝔪 : Ideal (𝓞 D.host.E)) (z : Mx D m n) :
    z ∈ hatMx (𝔪 • homLat Λ Λ') ↔ (∀ i j, infPart D (z i j) = 0) ∧
      ∀ i j, ∃ s ∈ idS D.host.F 𝔪, s.1 = fr β' β (z.map (toEAf D)) i j :=
  GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪 z

theorem fr_mem_idS (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ') {𝔪 : Ideal (𝓞 D.host.E)}
    {y : Matrix (Fin m) (Fin n) D.host.E} (hy : y ∈ 𝔪 • homLat Λ Λ') (i : Fin m) (j : Fin n) :
    ∃ s ∈ idS D.host.F 𝔪, s.1 = fr β' β (y.map (eToEAf D)) i j :=
  ((mem_hatMx_iff hβ hβ' 𝔪 _).1 (AddSubgroup.subset_closure ⟨1, fun v => by
    rw [map_one]; exact one_mem _, y, hy, rfl⟩)).2 i j

theorem sub_mem_of_mk_eq {𝔪 : Ideal (𝓞 D.host.E)} {y y' : homLat Λ Λ'} (h : Cos.mk 𝔪 y' = Cos.mk 𝔪 y) :
    y'.1 - y.1 ∈ 𝔪 • homLat Λ Λ' :=
  (Submodule.mem_smul_top_iff 𝔪 (homLat Λ Λ') (y' - y)).1 ((Submodule.Quotient.eq _).1 h)

theorem cpt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    infPart D e = 0 ∧ (∀ w ∈ P, cpt (D := D) w (toEAf D e) = 1) ∧ ∀ w ∉ P, cpt (D := D) w (toEAf D e) = 0 := by
  obtain ⟨⟨es, h, rfl⟩, -⟩ := he
  refine ⟨?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [hom_sum]
    exact Finset.sum_eq_zero fun Q hQ => (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) (h Q hQ)).1
  · rw [hom_sum, hom_sum, Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]
    exact (cpt_of_isIdemAt (h w hw)).1
  · rw [hom_sum, hom_sum]
    exact Finset.sum_eq_zero fun Q hQ => (cpt_of_isIdemAt (h Q hQ)).2 w fun h => hw (h ▸ hQ)

theorem mem_cosSet_iff (G : GridData L sc) (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ') {e : AE D} (he : IsIdemSum e G.pl.W0)
    (κ : Cos Λ Λ' G.modul) {x : Mx D m n} (hx : IsHalf e x) :
    x ∈ cosSet e κ ↔ ∀ w ∈ G.pl.W0, ∃ y : homLat Λ Λ', Cos.mk G.modul y = κ ∧ ∀ i j,
      Valued.v (cpt (D := D) w (fr β' β (x.map (toEAf D) - y.1.map (eToEAf D)) i j)) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  obtain ⟨e0, e1, e2⟩ := cpt_idemSum he
  have k1 : ∀ (y : Matrix (Fin m) (Fin n) D.host.E) i j, (x - e • y.map (incA D)) i j = e * (x i j - incA D (y i j)) :=
    fun y i j => by rw [mul_sub, hx]; rfl
  have k2 : ∀ (y : Matrix (Fin m) (Fin n) D.host.E) i j, fr β' β ((x - e • y.map (incA D)).map (toEAf D)) i j =
      toEAf D e * fr β' β (x.map (toEAf D) - y.map (eToEAf D)) i j := fun y i j => by
    have : (x - e • y.map (incA D)).map (toEAf D) = toEAf D e • (x.map (toEAf D) - y.map (eToEAf D)) :=
      Matrix.ext fun i j => by rw [Matrix.map_apply, k1, RingHom.map_mul, RingHom.map_sub]; rfl
    rw [this, fr_smul]; rfl
  constructor
  · rintro ⟨-, y, hy, hz⟩ w hw
    refine ⟨y, hy, fun i j => ?_⟩
    obtain ⟨s, hs, h⟩ := ((mem_hatMx_iff hβ hβ' _ _).1 hz).2 i j
    have := (mem_idS_modul G s).1 hs w hw
    rwa [h.trans (k2 _ i j), RingHom.map_mul, e1 w hw, one_mul] at this
  · intro h
    obtain ⟨y, hy⟩ : ∃ y, Cos.mk G.modul y = κ := Submodule.Quotient.mk_surjective _ κ
    refine ⟨hx, y, hy, (mem_hatMx_iff hβ hβ' _ _).2
      ⟨fun i j => by rw [k1, RingHom.map_mul, e0, zero_mul], fun i j => ?_⟩⟩
    have k3 : ∀ w ∈ G.pl.W0, Valued.v (cpt (D := D) w (fr β' β ((x - e • y.1.map (incA D)).map (toEAf D)) i j)) ≤
        WithZero.exp (-(cosExp G w : ℤ)) := fun w hw => by
      obtain ⟨y', hy', h'⟩ := h w hw
      obtain ⟨s, hs, h2⟩ := fr_mem_idS hβ hβ' (sub_mem_of_mk_eq (hy'.trans hy.symm)) i j
      have h3 := (mem_idS_modul G s).1 hs w hw
      have h4 := (k2 y.1 i j).trans (congrArg (toEAf D e * ·) (fr_sub_map β' β (eToEAf D) _ y.1 y'.1 i j))
      rw [h2] at h3
      exact v_mul_add_le h4 (e1 w hw) (h' i j) h3
    refine ⟨⟨_, (mem_OA_iff _).2 fun w => ?_⟩, (mem_idS_modul G _).2 k3, rfl⟩
    by_cases hw : w ∈ G.pl.W0
    · exact (k3 w hw).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    · exact cpt_mul_mem (k2 y.1 i j) (e2 w hw)

end Cosets

section Grid

variable {G : GridData L sc} (B : Frames G) (t : T) (w : Pl D.host.E)

theorem map_algebraMap {m n : ℕ} (y : Matrix (Fin m) (Fin n) D.host.E) :
    y.map (algebraMap D.host.E (Kw w)) = (y.map (eToEAf D)).map (cpt (D := D) w) :=
  Matrix.ext fun i j => (cpt_tmul w (y i j)).symm

theorem coord_mem_cosetSet {i : ℕ} (hi : i < D.R.m) (κ : G.CosAt i)
    (x : Matrix (Fin (G.V (.grid i 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) (EAf D)) :
    B.coord t w (X := (i, 0)) (Y := (i + 1, 0)) ⟨hi.le, Nat.zero_le _⟩ ⟨hi, Nat.zero_le _⟩ (x.map (cpt (D := D) w)) ∈
      cosetSet t w B hi κ ↔ ∃ y : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)), Cos.mk G.modul y = κ ∧ ∀ a b,
      Valued.v (cpt (D := D) w (fr (B.β i 0) (B.β (i + 1) 0) (x - y.1.map (eToEAf D)) a b)) ≤
        WithZero.exp (-(cosExp G w : ℤ)) := by
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [mem_matLat_pow, map_algebraMap, coord_map, coord_map, fr_sub]
  simp only [Matrix.sub_apply, RingHom.map_sub]
  exact ⟨fun H a b => H (b.cast (rank_vertex G t w (X := (i + 1, 0)) ⟨hi, Nat.zero_le _⟩).symm)
    (a.cast (rank_vertex G t w (X := (i, 0)) ⟨hi.le, Nat.zero_le _⟩).symm), fun H a b => H _ _⟩

theorem mem_cosSet_iff_cosetSet {μ₀ : T} (hL : L.Is μ₀) {e : AE D} (he : IsIdemSum e G.pl.W0) {i : ℕ} (hi : i < D.R.m)
    (κ : G.CosAt i) {x : Mx D (G.V (.grid i 0)).rank (G.V (.grid (i + 1) 0)).rank} (hx : IsHalf e x) :
    x ∈ cosSet e κ ↔ ∀ w ∈ G.pl.W0, B.coord t w (X := (i, 0)) (Y := (i + 1, 0)) ⟨hi.le, Nat.zero_le _⟩ ⟨hi, Nat.zero_le _⟩
      (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B hi κ :=
  (mem_cosSet_iff G (B.isFrame_β hL hi (Nat.zero_le _)) (B.isFrame_β hL hi.le (Nat.zero_le _)) he κ hx).trans
    (forall₂_congr fun w _ => (coord_mem_cosetSet B t w hi κ (x.map (toEAf D))).symm)

theorem cosetSet_of_notMem {μ₀ : T} (hL : L.Is μ₀) (hw : w ∉ G.pl.W0) {i : ℕ} (hi : i < D.R.m) (κ : G.CosAt i) :
    cosetSet t w B hi κ = {x | IntM x} := by
  have k : ∀ y : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)),
      B.coord t w (X := (i, 0)) (Y := (i + 1, 0)) ⟨hi.le, Nat.zero_le _⟩ ⟨hi, Nat.zero_le _⟩
        (y.1.map (algebraMap D.host.E (Kw w))) ∈ matLat _ (SplitFlip.stdLat (Kw w) _) := fun y => by
    rw [map_algebraMap, coord_map]
    refine mem_matLat_stdLat.2 fun a b => ?_
    obtain ⟨s, -, hs⟩ := fr_mem_idS (𝔪 := ⊤) (y := y.1) (B.isFrame_β hL hi (Nat.zero_le _))
      (B.isFrame_β hL hi.le (Nat.zero_le _)) (by rw [Submodule.top_smul]; exact y.2)
      (b.cast (rank_vertex G t w (X := (i, 0)) ⟨hi.le, Nat.zero_le _⟩))
      (a.cast (rank_vertex G t w (X := (i + 1, 0)) ⟨hi, Nat.zero_le _⟩))
    have := (mem_OA_iff _).1 s.2 w
    rw [hs] at this
    exact (vEq w).le_one_iff_le_one.2 this
  ext x
  rw [cosetSet, (depthAt_of_notMem G hw).1, pow_zero, one_smul]
  constructor
  · rintro ⟨y, -, h⟩
    exact mem_matLat_stdLat.1 (by simpa using add_mem h (k y))
  · intro h
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ κ
    exact ⟨y, hy, sub_mem (mem_matLat_stdLat.2 h) (k y)⟩

end Grid

section Red

variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K}

variable (φ ψ) in

structure IsRed : Prop where
  field : IsField κ
  int : ∀ s, ψ s ∈ 𝒪[K]
  ker : ∀ s, φ s = 0 ↔ valuation K (ψ s) < 1

variable (φ ψ) in

def Compat (c : κˣ →* ℂˣ) (μ : Kˣ →* ℂˣ) : Prop := ∀ (s : S) (u : κˣ) (k : Kˣ), u = φ s → k = ψ s → c u = μ k

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem IsRed.isUnit_iff (h : IsRed φ ψ) (s : S) : IsUnit (φ s) ↔ valuation K (ψ s) = 1 := by
  have := h.field.nontrivial
  have e : IsUnit (φ s) ↔ φ s ≠ 0 := ⟨IsUnit.ne_zero, fun h0 => by
    obtain ⟨b, hb⟩ := h.field.mul_inv_cancel h0
    exact IsUnit.of_mul_eq_one b hb⟩
  rw [e, Ne, h.ker, not_lt]
  exact ⟨le_antisymm (h.int s), fun h => h.ge⟩

theorem IsRed.isUnit_det_iff (h : IsRed φ ψ) {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n S) :
    IsUnit (M.map φ).det ↔ ∃ g ∈ KO K n, g.val = M.map ψ := by
  rw [show (M.map φ).det = φ M.det from (φ.map_det M).symm, h.isUnit_iff]
  constructor
  · intro h1
    let ψ' : S →+* 𝒪[K] := ψ.codRestrict _ h.int
    have h2 : IsUnit (M.map ψ').det := by
      rw [show (M.map ψ').det = ψ' M.det from (ψ'.map_det M).symm]
      exact (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.2 h1
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 h2
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change (algebraMap 𝒪[K] K).mapMatrix u.val = _
    rw [hu]; rfl
  · rintro ⟨g, hg, e⟩
    have := valuation_det_of_mem_KO hg
    rwa [Matrix.GeneralLinearGroup.val_det_apply, e, show (M.map ψ).det = ψ M.det from (ψ.map_det M).symm] at this

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem Compat.det {c : κˣ →* ℂˣ} {μ : Kˣ →* ℂˣ} (h : Compat φ ψ c μ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n S) {u : κˣ} {k : Kˣ} (hu : u = (M.map φ).det) (hk : k = (M.map ψ).det) : c u = μ k :=
  h M.det u k (hu.trans (φ.map_det M).symm) (hk.trans (ψ.map_det M).symm)

variable {r t : ℕ}

def IsIx {j a : ℕ} (e : Ix (Fin r) (Fin t) j ≃ Fin a) : Prop :=
  a = r + j * t ∧ (∀ i, (e (.inl i)).val = i.val) ∧ ∀ c s, (e (.inr (c, s))).val = r + (s.val + t * c.val)

theorem IsIx.blkOf {j a : ℕ} {e : Ix (Fin r) (Fin t) j ≃ Fin a} (h : IsIx e) (i : Ix (Fin r) (Fin t) j) :
    blkOf r t (e i) = i.blk := by
  rcases i with i | ⟨c, s⟩
  · rw [Formalism.L2.DIV.blkOf, if_pos (by rw [h.2.1]; exact i.2)]; rfl
  · rw [Formalism.L2.DIV.blkOf, h.2.2, if_neg (by omega), Nat.add_sub_cancel_left, Nat.add_mul_div_left _ _ s.pos,
      Nat.div_eq_of_lt s.2, zero_add]; rfl

variable {j j' a b : ℕ} {ea : Ix (Fin r) (Fin t) j ≃ Fin a} {eb : Ix (Fin r) (Fin t) j' ≃ Fin b}

theorem topL_r (ha : IsIx ea) (hb : IsIx eb) (y : Matrix (Fin b) (Fin a) κ) :
    topL r y = (y.submatrix eb ea).toBlocks₁₁ := by
  ext i l
  have h : i.val < b ∧ l.val < a := ⟨hb.2.1 i ▸ (eb _).2, ha.2.1 l ▸ (ea _).2⟩
  rw [topL, dif_pos h]
  exact congrArg₂ y (Fin.ext (hb.2.1 i).symm) (Fin.ext (ha.2.1 l).symm)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem lowZero_r (h : IsRed φ ψ) (ha : IsIx ea) (hb : IsIx eb) (N : Matrix (Fin b) (Fin a) S) :
    LowZero r (N.map φ) ↔ MaxM ((N.map ψ).submatrix eb ea).toBlocks₂₁ := by
  refine ⟨fun H i l => (h.ker _).1 (H _ _ (by rw [hb.2.2]; omega) (by rw [ha.2.1]; exact l.2)), fun H i l hi hl => ?_⟩
  obtain ⟨i | i, rfl⟩ := eb.surjective i
  · exact absurd (hb.2.1 i ▸ hi) i.2.not_ge
  obtain ⟨l | l, rfl⟩ := ea.surjective l
  · exact (h.ker _).2 (H i l)
  · rw [ha.2.2] at hl; omega

open Classical in

theorem parPhi_eq (h : IsRed φ ψ) (ha : IsIx ea) (hb : IsIx eb) {c : κˣ →* ℂˣ} {μ : Kˣ →* ℂˣ} (hc : Compat φ ψ c μ)
    (N : Matrix (Fin b) (Fin a) S) : parPhi μ⁻¹ ((N.map ψ).submatrix eb ea) =
      if H : LowZero r (N.map φ) ∧ IsUnit (topL r (N.map φ)).det then (c H.2.unit : ℂ) else 0 := by
  have e1 : topL r (N.map φ) = (N.submatrix eb ea).toBlocks₁₁.map φ := topL_r ha hb _
  split_ifs with H
  · obtain ⟨g, hg, e⟩ := (h.isUnit_det_iff _).1 (e1 ▸ H.2)
    rw [parPhi_of_mem (x := (N.map ψ).submatrix eb ea) _ hg e ((lowZero_r h ha hb N).1 H.1) (fun _ _ => h.int _) (fun _ _ => h.int _),
      MonoidHom.inv_apply, inv_inv, hc.det (k := Matrix.GeneralLinearGroup.det g) _ (H.2.unit_spec.trans (congrArg _ e1)) (congrArg Matrix.det e)]
  · by_contra h0
    obtain ⟨h1, h2, -⟩ := (parPhi_ne_zero_iff _).1 h0
    exact H ⟨(lowZero_r h ha hb N).2 h2, e1 ▸ (h.isUnit_det_iff _).2 h1⟩

def TopCond (t : ℕ) (hr : r ≤ a) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  g.val = topL a y ∧ g ∈ blockTri (blkOf r t) ∧ upperLeftBlock hr g = 1

variable {eb : Ix (Fin r) (Fin t) (j + 1) ≃ Fin b}

theorem val_succ_inl (ha : IsIx ea) (hb : IsIx eb) (i : Ix (Fin r) (Fin t) j) :
    (eb (ixSucc _ _ j (.inl i))).val = (ea i).val := by
  rcases i with i | ⟨c, s⟩
  · exact (hb.2.1 i).trans (ha.2.1 i).symm
  · exact (hb.2.2 c.castSucc s).trans (ha.2.2 c s).symm

theorem topL_a (ha : IsIx ea) (hb : IsIx eb) (y : Matrix (Fin b) (Fin a) κ) (i l : Ix (Fin r) (Fin t) j) :
    topL a y (ea i) (ea l) = y (eb (ixSucc _ _ j (.inl i))) (ea l) := by
  have h : (ea i).val < b ∧ (ea l).val < a := ⟨val_succ_inl ha hb i ▸ (eb _).2, (ea l).2⟩
  rw [topL, dif_pos h]
  exact congrArg₂ y (Fin.ext (val_succ_inl ha hb i).symm) rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem lowZero_a (h : IsRed φ ψ) (ha : IsIx ea) (hb : IsIx eb) (N : Matrix (Fin b) (Fin a) S) :
    LowZero a (N.map φ) ↔ MaxM (((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id).toRows₂ := by
  refine ⟨fun H i l => (h.ker _).1 (H _ _ ?_ (ea l).2), fun H i l hi _ => ?_⟩
  · have := hb.2.2 (Fin.last j) i
    rw [Fin.val_last, mul_comm] at this
    exact ha.1.le.trans (le_of_le_of_eq (by omega) this.symm)
  obtain ⟨i, rfl⟩ := eb.surjective i
  obtain ⟨l, rfl⟩ := ea.surjective l
  obtain ⟨i | i, rfl⟩ := (ixSucc _ _ j).surjective i
  · exact absurd (val_succ_inl ha hb i ▸ hi) (ea i).2.not_ge
  · exact (h.ker _).2 (H i l)

theorem diagonalBlock_det_blockTriangular (ha : IsIx ea) {g : GL (Fin a) κ} (hg : g ∈ blockTri (blkOf r t)) (c : Fin j) :
    (dBlk (blkOf r t) (c.val + 1) g : κ) = (Ix.diagonalBlockOfMatrix (g.val.submatrix ea ea) c).det := by
  have hb : Function.Bijective fun s : Fin t =>
      (⟨ea (.inr (c, s)), ha.blkOf _⟩ : {i : Fin a // blkOf r t i = c.val + 1}) := by
    refine ⟨fun s s' h => by simpa using congrArg Subtype.val h, fun ⟨i, hi⟩ => ?_⟩
    obtain ⟨i | ⟨c', s⟩, rfl⟩ := ea.surjective i
    · exact absurd ((ha.blkOf _).symm.trans hi) (Nat.succ_ne_zero _).symm
    · obtain rfl : c' = c := Fin.ext (Nat.succ_injective ((ha.blkOf _).symm.trans hi))
      exact ⟨s, rfl⟩
  rw [diag_block_det_val _ hg, ← det_submatrix_equiv_self (Equiv.ofBijective _ hb)]
  rfl

variable {μ : ℕ → Kˣ →* ℂˣ} (hμ : ∀ c, IsTame (μ c))

theorem mem_iter_iff (h : IsRed φ ψ) (ha : IsIx ea) (hr : r ≤ a) (M : Matrix (Ix (Fin r) (Fin t) j) (Ix (Fin r) (Fin t) j) S)
    {y : Matrix (Fin b) (Fin a) κ} (hy : (topL a y).submatrix ea ea = M.map φ) :
    (∃ g, TopCond t hr y g) ↔ ∃ g ∈ ((TypeDatum.principal K (Fin r)).iter (Fin t) μ hμ j).J, g.val = M.map ψ := by
  have e1 : ∀ g : GL (Fin a) κ, g.val = topL a y → (g ∈ blockTri (blkOf r t) ↔
      ∀ i l : Ix (Fin r) (Fin t) j, l.blk < i.blk → valuation K (ψ (M i l)) < 1) := fun g hg => by
    rw [mem_blockTri, hg, ea.surjective.forall₂]
    refine forall₂_congr fun i l => ?_
    rw [ha.blkOf, ha.blkOf, ← h.ker]
    exact imp_congr_right fun _ => iff_of_eq (congrArg (· = 0) (congrFun (congrFun hy i) l))
  have e2 : ∀ g : GL (Fin a) κ, g.val = topL a y → g ∈ blockTri (blkOf r t) →
      (upperLeftBlock hr g = 1 ↔ MaxM ((M.map ψ).toBlocks₁₁ - 1)) := fun g hg hb => by
    rw [Units.ext_iff, upper_block_val_submatrix hr (blockTri_blkOf_le r t hb), hg, ← Matrix.ext_iff]
    refine forall₂_congr fun i l => ?_
    have h1 : Fin.castLE hr i = ea (.inl i) := Fin.ext (ha.2.1 i).symm
    have h2 : Fin.castLE hr l = ea (.inl l) := Fin.ext (ha.2.1 l).symm
    have h3 : topL a y (ea (.inl i)) (ea (.inl l)) = φ (M (.inl i) (.inl l)) := congrFun (congrFun hy _) _
    have h4 := h.ker (M (.inl i) (.inl l) - if i = l then 1 else 0)
    rw [map_sub, map_sub, sub_eq_zero, apply_ite φ, apply_ite ψ, map_one, map_one, map_zero, map_zero] at h4
    rw [submatrix_apply, h1, h2, h3, Units.val_one, Matrix.one_apply]
    exact h4
  have e3 : (topL a y).det = (M.map φ).det := by rw [← hy, det_submatrix_equiv_self]
  constructor
  · rintro ⟨g, g1, g2, g3⟩
    obtain ⟨g', h1, h2⟩ := (h.isUnit_det_iff M).1 (e3 ▸ g1 ▸ (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
    exact ⟨g', ((GlobalTheory.StepData.iter_principal_spec μ hμ j).1 g').2 ⟨h1, h2 ▸ (e1 g g1).1 g2, h2 ▸ (e2 g g1 g2).1 g3⟩, h2⟩
  · rintro ⟨g', h1, h2⟩
    obtain ⟨k1, k2, k3⟩ := ((GlobalTheory.StepData.iter_principal_spec μ hμ j).1 g').1 h1
    obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (e3 ▸ (h.isUnit_det_iff M).2 ⟨g', k1, h2⟩)
    rw [h2] at k2 k3
    exact ⟨g, hg, (e1 g hg).2 k2, (e2 g hg ((e1 g hg).2 k2)).2 k3⟩

theorem iterPhi_ne_zero_iff (h : IsRed φ ψ) (ha : IsIx ea) (hb : IsIx eb) (hr : r ≤ a) (N : Matrix (Fin b) (Fin a) S) :
    (TypeDatum.principal K (Fin r)).iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) ≠ 0 ↔
      LowZero a (N.map φ) ∧ ∃ g, TopCond t hr (N.map φ) g := by
  rw [TypeDatum.iterPhi, TypeDatum.Phi_ne_zero_iff, lowZero_a h ha hb, and_comm,
    mem_iter_iff hμ h ha hr (N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea)
      (Matrix.ext (topL_a ha hb (N.map φ)))]
  rfl

theorem iterPhi_eq (h : IsRed φ ψ) (ha : IsIx ea) (hb : IsIx eb) (hr : r ≤ a) {χ : ℕ → κˣ →* ℂˣ}
    (hχ : ∀ c, c ≤ j → Compat φ ψ (χ (c + 1)) (μ (c + 1))) (N : Matrix (Fin b) (Fin a) S) (h0 : LowZero a (N.map φ))
    {g : GL (Fin a) κ} (hg : TopCond t hr (N.map φ) g) :
    (TypeDatum.principal K (Fin r)).iterPhi (Fin t) μ hμ j ((N.map ψ).submatrix eb ea) =
      (∏ c ∈ Finset.range j, (χ (c + 1) (dBlk (blkOf r t) (c + 1) g) : ℂ)) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹ := by
  set M := N.submatrix (fun i => eb (ixSucc _ _ j (.inl i))) ea
  have hy : (topL a (N.map φ)).submatrix ea ea = M.map φ := Matrix.ext (topL_a ha hb (N.map φ))
  obtain ⟨g', h1, h2⟩ := (mem_iter_iff hμ h ha hr M hy).1 ⟨g, hg⟩
  have e1 : ∀ c : Fin j, (dBlk (blkOf r t) (c.val + 1) g : κ) = ((Ix.diagonalBlockOfMatrix M c).map φ).det := fun c => by
    rw [diagonalBlock_det_blockTriangular ha hg.2.1, hg.1, hy]; rfl
  have e2 : ∀ c : Fin j, ∃ d : Kˣ, (d : K) = ((Ix.diagonalBlockOfMatrix M c).map ψ).det := fun c => by
    obtain ⟨d, -, hd⟩ := (h.isUnit_det_iff _).1 (e1 c ▸ Units.isUnit _)
    exact ⟨Matrix.GeneralLinearGroup.det d, congrArg Matrix.det hd⟩
  choose d hd using e2
  rw [TypeDatum.iterPhi, TypeDatum.Phi_of_mem (x := ((N.map ψ).submatrix eb ea).submatrix (ixSucc _ _ j) id) _ _
      ⟨g', h1⟩ h2 ((lowZero_a h ha hb N).1 h0),
    (GlobalTheory.StepData.iter_principal_spec μ hμ j).2 ⟨g', h1⟩ d (fun c => (hd c).trans (by rw [h2]; rfl)), Finset.prod_range, Units.coe_prod,
    Units.val_inv_eq_inv_val, ← (hχ j le_rfl).det M (u := Matrix.GeneralLinearGroup.det g)
      (by rw [← hy, det_submatrix_equiv_self, ← hg.1]; rfl) (congrArg Matrix.det h2)]
  exact congrArg (· * _) (Finset.prod_congr rfl fun c _ => by rw [(hχ c c.2.le).det _ (e1 c) (hd c)])

end Red

def cptO (w : Pl D.host.E) : OA D →+* Kw w := (cpt (D := D) w).comp (OA D).subtype

theorem cptO_apply (w : Pl D.host.E) (s : OA D) : cptO w s = cpt (D := D) w s.1 := RingHom.comp_apply _ _ _

theorem cptO_mem (w : Pl D.host.E) (s : OA D) : Valued.v (cptO w s) ≤ 1 := by
  rw [cptO_apply]; exact (mem_OA_iff _).1 s.2 w

theorem v_lt_one_iff {w : Pl D.host.E} (x : Kw w) : Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rw [← WithZero.exp_zero]
  exact ⟨fun h => WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h),
    fun h => h.trans_lt (by rw [WithZero.exp_lt_exp]; omega)⟩

theorem v_lt_one_congr {w : Pl D.host.E} {x y : Kw w} (h2 : Valued.v (x - y) < 1) : Valued.v y < 1 ↔ Valued.v x < 1 :=
  ⟨fun h => by simpa using Valuation.map_add_lt _ h2 h, fun h => by simpa using Valuation.map_sub_lt _ h h2⟩

theorem exists_resS_eq (w : Pl D.host.E) (s : OA D) : ∃ a : 𝓞 D.host.E, resS D.host.F w s = Ideal.Quotient.mk _ a ∧
    Valued.v (cptO w s - cptO w (oToS D.host.F D.host.E a)) < 1 := by
  obtain ⟨a, ha⟩ := exists_approx w.ne_bot s
  refine ⟨a, Eq.trans ?_ (resS_oToS (F := D.host.F) w a), ?_⟩
  · exact congrArg (RingEquiv.ofBijective (cmpS D.host.F w.asIdeal) (cmpS_bij _ w.ne_bot)).symm (Ideal.Quotient.eq.2 ha)
  · rw [← RingHom.map_sub, cptO_apply]
    exact (v_lt_one_iff _).2 (v_le_of_mem_idS (e := 1) (pow_one w.asIdeal).ge ha)

theorem mk_eq_zero_iff (w : Pl D.host.E) (a : 𝓞 D.host.E) :
    Ideal.Quotient.mk w.asIdeal a = 0 ↔ Valued.v (cptO w (oToS D.host.F D.host.E a)) < 1 := by
  rw [v_lt_one_iff, Ideal.Quotient.eq_zero_iff_mem, cptO_apply]
  exact ((v_oToS_le w a 1).trans (by rw [pow_one])).symm

theorem isRed (w : Pl D.host.E) : IsRed (resS D.host.F w) (cptO w) := by
  refine ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 w.isMaximal,
    fun s => (vEq w).le_one_iff_le_one.2 (cptO_mem w s), fun s => ?_⟩
  obtain ⟨a, h1, h2⟩ := exists_resS_eq w s
  exact ((iff_of_eq (congrArg (· = 0) h1)).trans (mk_eq_zero_iff w a)).trans
    ((v_lt_one_congr h2).trans (vEq w).lt_one_iff_lt_one.symm)

theorem compat_of_isRes {w : Pl D.host.E} {χ : HChar D.host.E} {c : (kP w)ˣ →* ℂˣ} (ht : χ.TameAt w) (hc : IsRes χ w c) :
    Compat (resS D.host.F w) (cptO w) c (χ.loc w) := by
  intro s u k hu hk
  obtain ⟨a, h1, h2⟩ := exists_resS_eq w s
  have := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  have h3 : Valued.v (cptO w (oToS D.host.F D.host.E a)) = 1 :=
    le_antisymm (cptO_mem w _)
      (not_lt.1 fun h => u.ne_zero ((hu.trans h1).trans ((mk_eq_zero_iff w a).2 h)))
  have h0 : cptO w (oToS D.host.F D.host.E a) = algebraMap D.host.E (Kw w) a :=
    (cptO_apply w _).trans (cpt_tmul w _)
  rw [h0] at h2 h3
  rw [← hk] at h2
  have h4 : (a : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero, map_zero] at h3
    exact zero_ne_one h3
  rw [hc a (Units.mk0 _ h4) u rfl (hu.trans h1), HChar.locK, MonoidHom.comp_apply, eq_comm, ← mul_inv_eq_one, ← map_inv,
    ← map_mul]
  refine isTame_loc ht _ ((vEq w).lt_one_iff_lt_one.2 ?_)
  have h5 : ((atFin w (Units.mk0 _ h4) : (Kw w)ˣ) : Kw w) = algebraMap D.host.E (Kw w) a := rfl
  rwa [Units.val_mul, Units.val_inv_eq_inv_val, ← mul_inv_cancel₀ (atFin w (Units.mk0 _ h4)).ne_zero, ← sub_mul, h5,
    map_mul, map_inv₀, h3, inv_one, mul_one]

open Classical in

theorem omegaG_eq_prod {a b r t j : ℕ} (hr : r ≤ a) (Pg Q : Finset (Pl D.host.E))
    (χ : ℕ → ∀ w : Pl D.host.E, (kP w)ˣ →* ℂˣ) (ξ : ∀ w : Pl D.host.E, (kP w)ˣ →* ℂˣ)
    (y : ∀ w : Pl D.host.E, Matrix (Fin b) (Fin a) (kP w)) (f : Pl D.host.E → ℂ)
    (h0 : ∀ w ∈ Pg, f w ≠ 0 → LowZero a (y w) ∧ ∃ g, TopCond t hr (y w) g)
    (h1 : ∀ w ∈ Pg, LowZero a (y w) → ∀ g, TopCond t hr (y w) g →
      f w = (∏ c ∈ Finset.range j, (χ (c + 1) w (dBlk (blkOf r t) (c + 1) g) : ℂ)) *
        (χ (j + 1) w (Matrix.GeneralLinearGroup.det g) : ℂ)⁻¹) :
    omegaG (Formalism.IndefR.Lev.datY a r t j hr Pg Q (LevelP.triv _ _ _) χ ξ .B) (χ (j + 1)) y = ∏ w ∈ Pg, f w := by
  rw [omegaG]
  split_ifs with H
  · have h2 := H.2.choose_spec
    rw [← Finset.prod_coe_sort Pg, Finset.prod_congr rfl fun (w : Pg) _ => h1 w.1 w.2 (H.1 w.1 w.2) (H.2.choose w)
      ⟨h2.1 w, h2.2.1 w, congrFun (Subgroup.mem_bot.1 h2.2.2) w⟩, Finset.prod_mul_distrib]
    exact congrArg (· * _) (one_mul _)
  · refine (Finset.prod_eq_zero_iff.2 (by_contra fun h => H ?_)).symm
    choose h2 g hg using fun w : Pg => h0 w.1 w.2 fun h' => h ⟨w.1, w.2, h'⟩
    exact ⟨fun w hw => h2 ⟨w, hw⟩, g, fun w => (hg w).1, fun w => (hg w).2.1,
      Subgroup.mem_bot.2 (funext fun w => (hg w).2.2)⟩

open Classical in

theorem omegaQ_eq_prod {a b : ℕ} (r : ℕ) (Q : Finset (Pl D.host.E)) (ξ : ∀ w : Pl D.host.E, (kP w)ˣ →* ℂˣ)
    (y : ∀ w : Pl D.host.E, Matrix (Fin b) (Fin a) (kP w)) : omegaQ Q r ξ 1 y =
      ∏ w ∈ Q, if H : LowZero r (y w) ∧ IsUnit (topL r (y w)).det then (ξ w H.2.unit : ℂ) else 0 := by
  rw [omegaQ]
  split_ifs with H
  · rw [← Finset.prod_attach Q]
    exact Finset.prod_congr rfl fun w _ => by rw [dif_pos (H w.1 w.2), zpow_one]
  · exact (Finset.prod_eq_zero_iff.2 (by_contra fun h0 => H fun w hw => by_contra fun h => h0 ⟨w, hw, dif_neg h⟩)).symm

section Steps

variable (G : GridData L sc) (t : T) (w : Pl D.host.E)

def ixOf {j a : ℕ} (h : a = D.R.r + j * D.R.t) : Ix (Fin D.R.r) (Fin D.R.t) j ≃ Fin a :=
  (ixFin G t w j).trans (finCongr (by change D.R.r + j * D.R.t + 0 * sLen D = a; rw [zero_mul, add_zero, h]))

theorem isIx_ixOf {j a : ℕ} (h : a = D.R.r + j * D.R.t) : IsIx (ixOf G t w h) := ⟨h, fun _ => rfl, fun _ _ => rfl⟩

theorem stepFn_of_mem_Pg (hw : w ∈ L.Pg) (j : ℕ) : stepFn L t w j = (TypeDatum.principal (Kw w) (Fin D.R.r)).iterPhi
    (Fin D.R.t) (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j := if_pos hw

theorem stepFn_of_mem_Q (hw : w ∉ L.Pg) (hw' : w ∈ L.Q t) (j : ℕ) : stepFn L t w j = parPhi ((L.xiH t).loc w)⁻¹ :=
  (if_neg hw).trans (if_pos hw')

theorem compat_chi {μ₀ : T} (hL : L.Is μ₀) (hw : w ∈ L.Pg) {c : ℕ} (hc : c < D.R.m) :
    Compat (resS D.host.F w) (cptO w) (L.chi (c + 1) w) ((muBase L (c + 1)).loc w)⁻¹ := fun s u k hu hk => by
  have h := compat_of_isRes ((L.C.isMu0 ⟨c, hc⟩).tame w) (hL.chi ⟨c, hc⟩ w hw) s u k hu hk
  rw [muBase, dif_pos hc, MonoidHom.inv_apply, ← h, MonoidHom.inv_apply, inv_inv]

open Classical in

theorem stepFn_eq_of_mem_Q {μ₀ : T} (hL : L.Is μ₀) (hw : w ∈ L.Q t) {j a b : ℕ} (ha : a = D.R.r + j * D.R.t)
    (hb : b = D.R.r + (j + 1) * D.R.t) (N : Matrix (Fin b) (Fin a) (OA D)) :
    stepFn L t w j ((N.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) =
      if H : LowZero D.R.r (N.map (resS D.host.F w)) ∧ IsUnit (topL D.R.r (N.map (resS D.host.F w))).det then
        (L.xiR t w H.2.unit : ℂ) else 0 := by
  have hw' : w ∉ L.Pg := fun h => Finset.disjoint_left.1 (GlobalTheory.StepLifts.places_apart L hL t).2 h hw
  refine (congrFun (stepFn_of_mem_Q t w hw' hw j) _).trans ?_
  exact parPhi_eq (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) (compat_of_isRes (hL.xi_tame t w) (hL.xiR t w hw)) N

open Classical in

theorem omega_eq_prod_stepFn {μ₀ : T} (hL : L.Is μ₀) {j a b : ℕ} (hj : j < D.R.m) (ha : a = D.R.r + j * D.R.t)
    (hb : b = D.R.r + (j + 1) * D.R.t) (hr : D.R.r ≤ a) (N : Matrix (Fin b) (Fin a) (EAf D)) (hN : IsIntM N) :
    omegaG (Formalism.IndefR.Lev.datY a D.R.r D.R.t j hr L.Pg (L.Q t) L.triv L.chi (L.xiR t) .B) (L.chi (j + 1))
        (fun PP => redM PP N) * omegaQ (L.Q t) D.R.r (L.xiR t) 1 (fun PP => redM PP N) =
      ∏ w ∈ L.Pg ∪ L.Q t, stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
  have hd := (GlobalTheory.StepLifts.places_apart L hL t).2
  obtain ⟨N', h1, h2⟩ : ∃ N' : Matrix (Fin b) (Fin a) (OA D), (fun PP => redM PP N) = (fun PP => N'.map (resS D.host.F PP)) ∧
      ∀ w, N.map (cpt (D := D) w) = N'.map (cptO w) :=
    ⟨fun i l => ⟨N i l, hN i l⟩, funext fun PP => Matrix.ext fun i l => dif_pos (hN i l),
      fun w => Matrix.ext fun i l => (cptO_apply w ⟨N i l, hN i l⟩).symm⟩
  simp only [h2]
  rw [h1, Finset.prod_union hd, omegaQ_eq_prod]
  refine congrArg₂ (· * ·) (omegaG_eq_prod hr _ _ _ _ _ _ (fun w hw => ?_) fun w hw k1 g k2 => ?_)
    (Finset.prod_congr rfl fun w hw => ?_)
  · rw [stepFn_of_mem_Pg t w hw]
    exact (iterPhi_ne_zero_iff (isTame_muBase w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr N').1
  · rw [stepFn_of_mem_Pg t w hw]
    exact iterPhi_eq (isTame_muBase w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr (χ := fun c => L.chi c w)
      (fun c hc => compat_chi w hL hw (hc.trans_lt hj)) N' k1 k2
  · exact (stepFn_eq_of_mem_Q G t w hL hw ha hb N').symm

end Steps

theorem rank_Yc {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t :=
  (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hj]; rfl)

theorem givenDatum_theta_coord {G : GridData L sc} (B : Frames G) (t : T) (w : Pl D.host.E) (Φ : G.Datum) {j : ℕ}
    (hj : j < D.R.m) (ha : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t)
    (hb : (G.V (.grid 0 (j + 1))).rank = D.R.r + (j + 1) * D.R.t)
    (x : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (EAf D)) :
    givenDatum t w B Φ (.theta 0 j) (B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩ ⟨Nat.zero_le _, hj.le⟩
      (x.map (cpt (D := D) w))) = stepFn L t w j (((fr (B.β 0 (j + 1)) (B.β 0 j) x).map (cpt (D := D) w)).submatrix
        (ixOf G t w hb) (ixOf G t w ha)) := by
  rw [coord_map]
  rfl

open Classical in

theorem local_factors {G : GridData L sc} (B : Frames G) (t : T) {μ₀ : T} (hL : L.Is μ₀) :
    (∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (i : ℕ) (hi : i < D.R.m) (κ : G.CosAt i)
      (x : Mx D (G.V (.grid i 0)).rank (G.V (.grid (i + 1) 0)).rank), IsHalf e x →
      (x ∈ cosSet e κ ↔ ∀ w ∈ G.pl.W0,
        B.coord t w (X := (i, 0)) (Y := (i + 1, 0)) ⟨hi.le, Nat.zero_le _⟩ ⟨hi, Nat.zero_le _⟩
          (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B hi κ)) ∧
    (∀ w ∉ G.pl.W0, ∀ (i : ℕ) (hi : i < D.R.m) (κ : G.CosAt i), cosetSet t w B hi κ = {x | IntM x}) ∧
    ∀ (j : ℕ) (hj : j < D.R.m) (b : ℕ) (hb : b = D.R.r + (j + 1) * D.R.t)
      (N : Matrix (Fin b) (Fin (Yc D j).rank) (EAf D)), IsIntM N →
      omegaG (L.datYt t j L.triv) (L.chi (j + 1)) (fun PP => redM PP N) *
          omegaQ (L.Q t) D.R.r (L.xiR t) 1 (fun PP => redM PP N) =
        ∏ w ∈ L.Pg ∪ L.Q t, stepFn L t w j
          ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w (rank_Yc hj.le))) :=
  ⟨fun _ he _ hi κ _ hx => mem_cosSet_iff_cosetSet B t hL he hi κ hx, fun w hw _ hi κ => cosetSet_of_notMem B t w hL hw hi κ,
    fun j hj _ hb N hN => omega_eq_prod_stepFn G t hL hj (rank_Yc hj.le) hb (r_le_Y j) N hN⟩

end GlobalTheory.FunObj.Comparison₂

end
