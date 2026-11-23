import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

private theorem multiset_eq_of_esymm (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → M.esymm k = M'.esymm k) : M = M' := by
  have hp : (M.map fun a => Polynomial.X - Polynomial.C a).prod = (M'.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, h1, h2]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [Multiset.esymm]
    · rw [h k hk0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [← Polynomial.roots_multiset_prod_X_sub_C M, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem multiset_eq_of_norm (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r) (q u : ℂ) (n : ℕ)
    (hq : q ≠ 0) (hu : u ≠ 0)
    (h : ∀ k, 1 ≤ k → k ≤ r → q ^ (k * (r - k) / 2) * (M.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k =
      q ^ (k * (r - k) / 2) * (M'.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k) : M = M' := by
  have hinj : Function.Injective fun a : ℂ => a⁻¹ * u⁻¹ * (q ^ n)⁻¹ := fun a b hab =>
    inv_injective (mul_right_cancel₀ (inv_ne_zero hu) (mul_right_cancel₀ (inv_ne_zero (pow_ne_zero _ hq)) hab))
  refine Multiset.map_injective hinj (multiset_eq_of_esymm _ _ r (by rw [Multiset.card_map, h1])
    (by rw [Multiset.card_map, h2]) fun k a b => mul_left_cancel₀ (pow_ne_zero _ hq) (h k a b))

private theorem isRepOf_of_split (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₂ : IsRepOf D l ι π s ρ₂)
    (c₁ : Continuous (fun g => ((ρ₁ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))) (s₁ : IsSSRep ρ₁)
    (f₁ : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((ρ₁ σ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) : IsRepOf D l ι π s ρ₁ := by
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hs, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 hs B g hB hg, hw.2 B g hB hg])
  refine ⟨c₁, s₁, f₂.mono fun w hw B σ hB hσ => ?_⟩
  rw [hcp σ]
  exact hw B σ hB hσ

private theorem side_data (D : D7) (cf : CharFrame D) (hCS : CharSide D cf) (Rw : RowSide D) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (hE : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) (S : RatDat D.ntw)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT)
    (hR : RowEig D S eig c rowS) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hi : D.what₂.isot (D.ntw.jS i s) (rowS i s) ≠ ⊥) (hg : D.nd.goodRow (rowS i s)) (π : D.naut.CG D.R.r)
    (hπ : ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR (rowS i s) w) (j : Fin D.R.m) (hj : j.1 + 1 = D.ntw.jS i s)
    (t : ℝ) (P : PlE D.host) (hP : IsSplitPl D.host P) (h1 : P ∉ Sb) (h2 : P ∉ D.ntw.S0 i) :
    ∃ M : Multiset ℂ, M.card = D.R.r ∧
      galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) P) t) =
        (((M.map (· * ((cf.eta.val P : ℂˣ) : ℂ))).map (· * ((normV P : ℕ) : ℂ) ^ ((t : ℝ) : ℂ))).map
          fun α => Polynomial.X - Polynomial.C α).prod ∧
      ∀ k, 1 ≤ k → k ≤ D.R.r → ∃ x : ↥D.LL0, embLL0 D x = ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * (M.map fun a =>
        a⁻¹ * (((cf.mu0 j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹).esymm k ∧
        algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
          algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i (D.ntw.side i s) P) ^ k *
            IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
              (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
              ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x) := by
  obtain ⟨hu, he⟩ := hE j (rowS i s) (by rw [hj]; exact hi) hg P hP h1
  rw [← hπ P hP] at hu he
  refine ⟨D.naut.frobEig (D.naut.locG π P), by rw [D.naut.frobEig_card _ hu, D.naut.locG_dim], ?_, fun k a b => ?_⟩
  · have hue : D.naut.unr (D.naut.locG D.naut.etaTinv P) := (D.naut.etaTinv_def P).1
    have hfe : D.naut.frobEig (D.naut.locG D.naut.etaTinv P) = {((cf.eta.val P : ℂˣ) : ℂ)} := by
      rw [hCS.frob _ P ((hCS.unr_iff _ P).1 hue), hCS.etaTinv, HChar.val_inv, inv_inv]
    have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv P) = 1 := D.naut.locG_dim _ P
    rw [galPol, D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hd hu hue),
      D.naut.frobEig_char _ _ _ hu hue hd hfe]
  · refine ⟨eig (D.ntw.jS i s) (rowS i s) k P, ?_, hR i s k P a b hP h2⟩
    have := he k a b
    rw [hj] at this
    exact this

private theorem read_cancel (D : D7) (i : D.ntw.Tw) (b : Bool) (u : (D.ntw.O i)ˣ) (k : ℕ) (x y : ↥D.LL0)
    (h : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) y)) : x = y :=
  RingHom.injective _ (RingHom.injective _ (mul_left_cancel₀ (pow_ne_zero _ (u.isUnit.map _).ne_zero) h))

theorem UpperTheory.galoisRep_transport_of_copyAll :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → ∀ (Rw : RowSide D) (jE' : D'.host.E →+* Qb) (A' : SideA D' cf' jE'), RowCusp D Rw → GalEx D' → GlobalTheory.RowTie.ChebSplit D'.nd → ∀ (Sb : Finset (PlE D.host)) (Sb' : Finset (PlE D'.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (eig' : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.TwInputs.EigTrue D' cf' A'.row Sb' eig' → ∀ (S : RatDat D.ntw) (S' : RatDat D'.ntw) (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ), SameUnits c c' → ∀ (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) (rowS' : ∀ i, D'.ntw.Sig i → D'.what₂.FT), RowEig D S eig c rowS → RowEig D' S' eig' c' rowS' → RhoSpec D Rw rowS → (∀ i s, D'.what₂.isot (D'.ntw.jS i s) (rowS' i s) ≠ ⊥ ∧ D'.nd.goodRow (rowS' i s)) → RhoSpec D' A'.row rowS' := by
  intro hGA D D' ι e h cf cf' hF hCS Rw jE' A' hRC hGal hCh Sb Sb' eig eig' hE hE' S S' c c' hU rowS rowS' hR hR' hρ hgood
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  intro i s
  refine ⟨(hgood i s).1, (hgood i s).2, fun π' hc hr hloc φ ιq hφ hι => ?_⟩
  obtain ⟨hi, hg, hspec⟩ := hρ i s
  have hjr := D.ntw.jS_range i s
  obtain ⟨π, pc, pr, ploc, -⟩ := hRC _ hjr.1 hjr.2 _ hi hg
  have hemb : ∀ x, (if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) (e x) =
      (if (overD D r).ntw.side i s then (overD D r).ntw.emb0 i else (overD D r).ntw.emb0b i) x := by
    intro x
    have e1 := eq_of_heq (h.cp.emb0 i i HEq.rfl x)
    have e2 := eq_of_heq (h.cp.emb0b i i HEq.rfl x)
    have e3 : (overD D r).ntw.side i s = D.ntw.side i s := rfl
    rw [e3]
    cases D.ntw.side i s
    · exact e2
    · exact e1
  have hι0 : ∀ x : ↥D.LL0, ιq (φ ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hemb y, h.cp.embLL0_eq]
    exact hι y
  obtain ⟨c1, s1, f1⟩ := hspec π pc pr ploc φ ιq hφ hι0
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw hGA _ cf' jE' A' hGal _ ιq π' hc hr
  refine isRepOf_of_split _ ιq _ _ hCh _ ρ' hρ' c1 s1 ?_
  have hmu : cf.mu0 = cf'.mu0 := eq_of_heq hF.mu0
  have heta : cf.eta = cf'.eta := eq_of_heq hF.eta
  have hcc : ∀ b P, c' i b P = c i b P := fun b P => eq_of_heq (hU i i b P P HEq.rfl HEq.rfl)
  have hj : (⟨D.ntw.jS i s - 1, by omega⟩ : Fin D.R.m).1 + 1 = D.ntw.jS i s := Nat.sub_add_cancel hjr.1
  filter_upwards [f1, Sb.eventually_cofinite_notMem, Sb'.eventually_cofinite_notMem,
    (D.ntw.S0 i).eventually_cofinite_notMem] with P hP n1 n2 n3 hs B σ hB hσ
  obtain ⟨M, m1, m2, m3⟩ := side_data D cf hCS Rw Sb eig hE S c rowS hR i s hi hg π ploc _ hj
    ((1 - (D.R.nV : ℝ)) / 2) P hs n1 n3
  obtain ⟨M', m1', m2', m3'⟩ := side_data _ cf' A'.chr A'.row Sb' eig' hE' S' c' rowS' hR' i s (hgood i s).1 (hgood i s).2
    π' hloc _ hj ((1 - (D.R.nV : ℝ)) / 2) P hs n2 n3
  have hq : ((normV P : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  have hM : M = M' := by
    refine multiset_eq_of_norm M M' D.R.r m1 m1' _ _ (D.R.nV / 2) hq
      ((cf.mu0 ⟨D.ntw.jS i s - 1, by omega⟩).val P).ne_zero fun k a b => ?_
    obtain ⟨x, x1, x2⟩ := m3 k a b
    obtain ⟨y, y1, y2⟩ := m3' k a b
    rw [← hmu] at y1
    rw [← hemb y, hcc] at y2
    have hxy : x = e y := read_cancel D i _ _ k _ _ (x2.symm.trans y2)
    refine x1.symm.trans (Eq.trans ?_ y1)
    rw [hxy, h.cp.embLL0_eq]
  subst hM
  rw [← heta] at m2'
  exact (hP B σ hB hσ).trans (m2.trans m2'.symm)
