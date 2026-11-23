import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.LevBack
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (framePos)
open GlobalTheory.SymBridge (IsOrd zPos)
open GlobalTheory.AdelicLatMove (finEmb finEmb_mul)
open Formalism.L2.DIV (blockTri blkOf blk2 upperLeftBlock resS oToS idS kP frGL St redFn)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem pr_e : q.pr q.e = 1 := by rw [← sec_one, q.pr_sec]

theorem toEAf_finEmb (t : EAf D) : toEAf D (finEmb D t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, RingHom.map_zero]
  | add a b ha hb => rw [map_add, RingHom.map_add, ha, hb]
  | tmul x α => rfl

theorem toEAf_mem_iff (a : AE D) : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ finPart D a ∈ intAE D :=
  (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).symm

theorem finEmb_mul' (x y : EAf D) : finEmb D (x * y) = finEmb D x * finEmb D y := by
  rw [← finEmb_mul, toEAf_finEmb]

theorem pr_finEmb_one {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) : q.pr (finEmb D 1) = 1 := by
  have h1 : IsIdempotentElem (q.pr (finEmb D 1)) := by rw [IsIdempotentElem, ← map_mul, ← finEmb_mul', mul_one]
  refine (IsIdempotentElem.iff_eq_zero_or_one.1 h1).resolve_left fun h0 => ?_
  have h2 : toEAf D q.e = 0 := by
    have := congrArg (toEAf D) (q.sec_pr (finEmb D 1))
    rwa [h0, map_zero, map_zero, map_mul, toEAf_finEmb, mul_one, eq_comm] at this
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
  refine (h.2 x hx0).1 hx ?_
  rw [← toEAf_mem_iff, map_mul, h2, zero_mul]
  exact zero_mem _

theorem pr_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (q.pr (incA D (z : D.host.E))) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : (q.pr.comp (incA D)) (z : D.host.E) ≠ 0 :=
    (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k ((q.pr.comp (incA D)) (z : D.host.E))) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem exists_chart {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) : ∃ π : EAf D →+* k, (∀ a, π (toEAf D a) = q.pr a) ∧
    (∀ z, toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ π z ∈ 𝒪[k]) ∧
    (∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[k]) ∧
    ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation k (π s) < 1 := by
  let π : EAf D →+* k :=
    { toFun := fun z => q.pr (finEmb D z)
      map_one' := pr_finEmb_one q h
      map_mul' := fun x y => by rw [finEmb_mul', map_mul]
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun x y => by rw [map_add, map_add] }
  have h1 : ∀ a, π (toEAf D a) = q.pr a := fun a => by
    change q.pr (finEmb D _) = _
    rw [← mul_one (toEAf D a), finEmb_mul, map_mul, pr_finEmb_one q h, mul_one]
  have h2 : ∀ z, toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ π z ∈ 𝒪[k] := fun z => by
    rw [q.int_iff, ← toEAf_mem_iff]
    change _ ↔ toEAf D (q.sec (q.pr _)) ∈ _
    rw [q.sec_pr, map_mul, toEAf_finEmb]
  have hf : toEAf D q.e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (h2 1).2 (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at this
  have h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[k] := fun s => (h2 _).1 (mul_mem hf s.2)
  have h4 : ∀ a, π (oToS D.host.F D.host.E a) = q.pr (incA D (a : D.host.E)) := fun a => h1 (incA D (a : D.host.E))
  have h5 : ∀ s ∈ idS D.host.F PP.asIdeal, valuation k (π s) < 1 := fun s hs => by
    refine Submodule.span_induction (p := fun s _ => valuation k (π (s : Formalism.L2.Herm.intAf D.host.F D.host.E)) < 1)
      ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨a, ha, rfl⟩
      rw [h4]
      exact (pr_lt q h a).1 ha
    · simp
    · intro x y _ _ hx hy
      rw [Subring.coe_add, RingHom.map_add]
      exact Valuation.map_add_lt _ hx hy
    · intro c x _ hx
      rw [smul_eq_mul, Subring.coe_mul, RingHom.map_mul, Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (h3 c)) hx
  refine ⟨π, h1, h2, h3, fun s => ?_⟩
  obtain ⟨c, hc⟩ := Formalism.L2.DIV.cmpS_surj (F := D.host.F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have ha : s - oToS D.host.F D.host.E a ∈ idS D.host.F PP.asIdeal := Ideal.Quotient.eq.1 hc.symm
  have h6 : resS D.host.F PP s = Ideal.Quotient.mk _ a := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F), ← sub_eq_zero, ← map_sub]
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  have h7 := h5 _ ha
  rw [AddSubgroupClass.coe_sub, RingHom.map_sub, h4] at h7
  rw [h6, Ideal.Quotient.eq_zero_iff_mem, pr_lt q h]
  constructor
  · intro h8
    simpa using Valuation.map_add_lt _ h7 h8
  · intro h8
    simpa using Valuation.map_sub_lt _ h8 h7

theorem pr_other {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q' : SplitPt D k')
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {a : AE D} (ha : IsIdemSum a P) {PP PP' : Formalism.L2.DIV.Pl D.host.E}
    (h : PP ∈ P) (h' : PP' ∈ P) (hne : PP' ≠ PP) (he : IsIdemAt q.e PP) (he' : IsIdemAt q'.e PP') :
    q'.pr (q.e + cA D q.e) = 0 := by
  have h1 : q'.e * cA D q.e = 0 := by
    rw [← GlobalTheory.DiagLiftFix.idemSum_mul ha h he, ← GlobalTheory.DiagLiftFix.idemSum_mul ha h' he', RingHom.map_mul, mul_mul_mul_comm, ha.2,
      zero_mul]
  have h2 : q'.pr (cA D q.e) = 0 := by
    have := congrArg q'.pr h1
    rwa [map_mul, pr_e, one_mul, map_zero] at this
  rw [map_add, h2, add_zero]
  have i1 : IsIdempotentElem (q'.pr q.e) := by rw [IsIdempotentElem, ← map_mul, he.1.1]
  have i2 : IsIdempotentElem (q.pr q'.e) := by rw [IsIdempotentElem, ← map_mul, he'.1.1]
  refine (IsIdempotentElem.iff_eq_zero_or_one.1 i1).resolve_right fun h3 => ?_
  have h4 : q'.e = q'.e * q.e := by rw [← q'.sec_pr, h3, sec_one]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 i2 with h5 | h5
  · have h6 := pr_e q'
    rw [h4, mul_comm, ← q.sec_pr, h5, map_zero, map_zero] at h6
    exact zero_ne_one h6
  · have h6 : q.e = q'.e := by rw [h4, mul_comm, ← q.sec_pr, h5, sec_one]
    refine hne (HeightOneSpectrum.ext (Ideal.ext fun x => ?_))
    by_cases hx : x = 0
    · simp [hx]
    · rw [he.2 x hx, he'.2 x hx, h6]

end Place

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blkOf_zPos {κ l t j n r : ℕ} (hr : r = κ + l) {e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin n} (he : IsOrd zPos e)
    (a : Ix (Fin κ ⊕ Fin l) (Fin t) j) : blkOf r t (e a) = Sum.elim (fun _ => 0) (fun p => p.1.val + 1) a := by
  unfold blkOf
  rw [he a]
  rcases a with (a | a) | ⟨p, i⟩
  · rw [if_pos (by have := a.2; simp only [zPos]; omega)]; rfl
  · rw [if_pos (by have := a.2; simp only [zPos]; omega)]; rfl
  · rw [if_neg (by simp only [zPos]; omega)]
    have ht : 0 < t := i.pos
    have : zPos (κ := κ) (l := l) (Sum.inr (p, i)) - r = i.val + t * p.val := by
      simp only [zPos, mul_comm t]; omega
    rw [this, Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt i.2, zero_add]
    rfl

theorem red_of_pattern {s κ t j n r : ℕ} (S : SymData k s κ) (hr0 : r = κ + (s + 1)) (hr : r ≤ n)
    {e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j ≃ Fin n} (he : IsOrd zPos e) {O K : Type} [CommRing O] [CommRing K] [Nontrivial K]
    (φ : O →+* K) (ψ : O →+* k) (h1 : ∀ z, ψ z ∈ 𝒪[k]) (h2 : ∀ z, φ z = 0 ↔ valuation k (ψ z) < 1) (Y : GL (Fin n) O)
    (hy : ∀ a b, ¬ FreeIx S.ρ a b → valuation k (ψ (Y.val (e a) (e b)) - (1 : Matrix _ _ k) a b) < 1) :
    Formalism.UG.bc φ Y ∈ blockTri (blkOf r t) ∧ ∃ x : S.P.J, ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = framePos _ _ a →
      b'.val = framePos _ _ b → ∀ z : O, φ z = (upperLeftBlock hr (Formalism.UG.bc φ Y)).val a' b' →
        valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - ψ z) < 1 := by
  have hb : Formalism.UG.bc φ Y ∈ blockTri (blkOf r t) := by
    intro i j' hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j'
    rw [blkOf_zPos hr0 he, blkOf_zPos hr0 he] at hij
    have h3 : ¬ FreeIx S.ρ a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp [FreeIx] at hij ⊢
      exact hij
    have h4 := hy a b h3
    rw [one_apply_ne (by rintro rfl; exact lt_irrefl _ hij), sub_zero] at h4
    exact (h2 _).2 h4
  refine ⟨hb, ?_⟩
  have hv := Formalism.L2.DIV.upper_block_val_submatrix hr (Formalism.L2.DIV.blockTri_blkOf_le _ _ hb)
  let e₀ : Fin κ ⊕ Fin (s + 1) ≃ Fin r := finSumFinEquiv.trans (finCongr hr0.symm)
  have he₀ : ∀ a, (e₀ a).val = framePos _ _ a := by rintro (a | a) <;> simp [e₀, framePos]
  have hc : ∀ a (a' : Fin r), a'.val = framePos _ _ a → Fin.castLE hr a' = e (Sum.inl a) := fun a a' h =>
    Fin.ext (by rw [he]; rcases a with a | a <;> exact h)
  let Z : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) O := fun a b => Y.val (e (Sum.inl a)) (e (Sum.inl b))
  have hZ : ∀ a b (a' b' : Fin r), a'.val = framePos _ _ a → b'.val = framePos _ _ b →
      (upperLeftBlock hr (Formalism.UG.bc φ Y)).val a' b' = φ (Z a b) := fun a b a' b' ha hb => by
    rw [hv, submatrix_apply, hc a a' ha, hc b b' hb]
    rfl
  let p : O →+* 𝒪[k] := ψ.codRestrict _ h1
  have hd : IsUnit (p.mapMatrix Z).det := by
    by_contra hn
    have h3 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn
    rw [← RingHom.map_det] at h3
    have h4 := (h2 _).2 h3
    have h5 : φ.mapMatrix Z = (upperLeftBlock hr (Formalism.UG.bc φ Y)).val.submatrix e₀ e₀ :=
      Matrix.ext fun a b => (hZ a b _ _ (he₀ a) (he₀ b)).symm
    rw [RingHom.map_det, h5, det_submatrix_equiv_self] at h4
    have h6 := ((upperLeftBlock hr (Formalism.UG.bc φ Y)).det).isUnit
    rw [GeneralLinearGroup.val_det_apply, h4] at h6
    exact not_isUnit_zero h6
  let x₀ : GL (Fin κ ⊕ Fin (s + 1)) 𝒪[k] := ((isUnit_iff_isUnit_det _).2 hd).unit
  refine ⟨⟨GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀, (SymData.mem_J_iff_pattern k s κ S _).2 ⟨⟨x₀, rfl⟩, fun a b hab => ?_⟩⟩,
    fun a b a' b' ha hb z hz => ?_⟩
  · have := hy (Sum.inl a) (Sum.inl b) hab
    rw [show (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) j) _ k) (Sum.inl a) (Sum.inl b) = (1 : Matrix _ _ k) a b by
      simp [one_apply]] at this
    exact this
  · change valuation k (ψ (Z a b) - ψ z) < 1
    rw [← map_sub, ← h2, map_sub, hz, hZ a b a' b' ha hb, sub_self]

theorem conj_frame {N : ℕ} {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    (L : LatFrame k ι Y) (e : ι ≃ Fin N) (B X : GL (Fin N) k) (y : GL ι k)
    (hB : B.val = (F.β * L.bas.val).submatrix id fun i => L.ord (e.symm i)) (hX : X.val = F.β * (L.conj y).val * F.γ) :
    B⁻¹ * X * B = reGL e y := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hX, hB, reGL_val, LatFrame.conj_apply]
  have h1 : F.β * (L.bas * reGL L.ord y * L.bas⁻¹).val * F.γ * (F.β * L.bas.val) = F.β * L.bas.val * (reGL L.ord y).val := by
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]
  have h2 : y.val.submatrix e.symm e.symm = (reGL L.ord y).val.submatrix (e.symm.trans L.ord) (e.symm.trans L.ord) := by
    rw [reGL_val]
    ext i j
    simp
  rw [h2]
  change _ = (F.β * L.bas.val).submatrix id (e.symm.trans L.ord) * _
  rw [submatrix_mul_equiv, ← h1]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id, Equiv.trans_apply]

end Loc

theorem exists_int_ring {R : Type} [CommRing R] (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) {n : ℕ}
    (B X γ : GL (Fin n) R) (hγ : γ = B⁻¹ * X * B) (b0 : ∀ i j, (f + f') * (X.val - 1) i j = (X.val - 1) i j)
    (a1 : ∀ i j, (f • γ.val) i j ∈ O) (a2 : ∀ i j, (f • (γ⁻¹).val) i j ∈ O)
    (a3 : ∀ i j, (f' • γ.val) i j ∈ O) (a4 : ∀ i j, (f' • (γ⁻¹).val) i j ∈ O) :
    ∃ Y : GL (Fin n) O, Formalism.UG.bc O.subtype Y = γ ∧
      ∀ i j, (f + f') * ((Y.val i j : R) - (1 : Matrix _ _ R) i j) = (Y.val i j : R) - (1 : Matrix _ _ R) i j := by
  have b0' : (f + f') • (X.val - 1) = X.val - 1 := Matrix.ext b0
  have b1 : (f + f') • (γ.val - 1) = γ.val - 1 := by
    have e : γ.val - 1 = (B⁻¹).val * (X.val - 1) * B.val := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, hγ, Units.val_mul, Units.val_mul]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, b0']
  have b2 : (f + f') • ((γ⁻¹).val - 1) = (γ⁻¹).val - 1 := by
    have e : (γ⁻¹).val - 1 = -((γ⁻¹).val * (γ.val - 1)) := by
      rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, b1]
  have key : ∀ A : Matrix (Fin n) (Fin n) R, (f + f') • (A - 1) = A - 1 → (∀ i j, (f • A) i j ∈ O) →
      (∀ i j, (f' • A) i j ∈ O) → ∀ i j, A i j ∈ O := fun A c1 c2 c3 i j => by
    have c4 : (f + f') * (A i j - (1 : Matrix _ _ R) i j) = A i j - (1 : Matrix _ _ R) i j := congrFun (congrFun c1 i) j
    have c5 : A i j = f * A i j + f' * A i j + (1 - (f + f')) * (1 : Matrix _ _ R) i j := by
      linear_combination -c4
    rw [c5]
    refine add_mem (add_mem (c2 i j) (c3 i j)) (mul_mem (sub_mem (one_mem _) (add_mem hf hf')) ?_)
    rw [one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  let Ym : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, key _ b1 a1 a3 i j⟩
  let Ym' : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, key _ b2 a2 a4 i j⟩
  have hm : Ym.map O.subtype = γ.val := rfl
  have hm' : Ym'.map O.subtype = (γ⁻¹).val := rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) := by
    intro M N h
    ext i j
    exact congrFun (congrFun h i) j
  have e1 : Ym * Ym' = 1 := inj (by
    show (Ym * Ym').map O.subtype = (1 : Matrix _ _ O).map O.subtype
    rw [Matrix.map_mul, hm, hm', Units.mul_inv, Matrix.map_one _ O.subtype.map_zero O.subtype.map_one])
  have e2 : Ym' * Ym = 1 := inj (by
    show (Ym' * Ym).map O.subtype = (1 : Matrix _ _ O).map O.subtype
    rw [Matrix.map_mul, hm, hm', Units.inv_mul, Matrix.map_one _ O.subtype.map_zero O.subtype.map_one])
  exact ⟨⟨Ym, Ym', e1, e2⟩, Units.ext hm, fun i j => congrFun (congrFun b1 i) j⟩

theorem conj_conj {G : Type} [Group G] (b t x : G) : b⁻¹ * (t⁻¹ * x * t) * b = (t * b)⁻¹ * x * (t * b) := by group

theorem conj_back {G : Type} [Group G] (b h : G) : b * (b⁻¹ * h * b) * b⁻¹ = h := by group

section Glob
variable {D : D7}

theorem exists_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
    (π : EAf D →+* k) (h2 : ∀ z, toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ π z ∈ 𝒪[k])
    (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (EAf D)} (hΛ : IsSelfDualC V Λ)
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {t x : GA D V} (hx : SuppAt q.e V x)
    (hK : GeneralLinearGroup.map π (β⁻¹ * Lev.finE V (t⁻¹ * x * t) * β) ∈ KO k _) :
    ∃ Y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), frGL β Y = Lev.finE V (t⁻¹ * x * t) ∧
      (∀ i j, (Y.val i j : EAf D) = (β⁻¹ * Lev.finE V (t⁻¹ * x * t) * β).val i j) ∧
      ∀ i j, toEAf D (q.e + cA D q.e) * ((Y.val i j : EAf D) - (1 : Matrix _ _ (EAf D)) i j) =
        (Y.val i j : EAf D) - (1 : Matrix _ _ (EAf D)) i j := by
  rw [mem_KO, ← MonoidHom.map_inv] at hK
  have a1 : IsIntM (toEAf D q.e • (β⁻¹ * Lev.finE V (t⁻¹ * x * t) * β).val) := fun i j => (h2 _).2 (hK.1 i j)
  have a2 : IsIntM (toEAf D q.e • ((β⁻¹ * Lev.finE V (t⁻¹ * x * t) * β)⁻¹).val) := fun i j => (h2 _).2 (hK.2 i j)
  obtain ⟨a3, a4⟩ := GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ β hΛ hβ _ (GlobalTheory.LevSplit.finE_mem_UA V _) _ rfl q.e a1 a2
  have hf : toEAf D q.e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (h2 1).2 (by rw [RingHom.map_one]; exact one_mem _)
    rwa [mul_one] at this
  have hf' : toEAf D (cA D q.e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [GlobalTheory.AdelicLatMove.toEAf_cA]
    exact GlobalTheory.LevSplit.sigR_int hf
  have b0 : ∀ i j, (toEAf D q.e + toEAf D (cA D q.e)) * ((Lev.finE V x).val - 1) i j = ((Lev.finE V x).val - 1) i j := by
    have e : (Lev.finE V x).val - 1 = (mt V x - 1).map (toEAf D) := by
      rw [Matrix.map_sub _ (toEAf D).map_sub, Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one]
      rfl
    intro i j
    rw [e, ← RingHom.map_add]
    exact ((toEAf D).map_mul _ _).symm.trans (congrArg (toEAf D) (hx i j))
  obtain ⟨Y, hY, hY1⟩ := exists_int_ring _ hf hf' (Lev.finE V t * β) (Lev.finE V x) _ (by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, conj_conj]) b0 a1 a2 a3 a4
  refine ⟨Y, ?_, fun i j => congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val i j) hY, fun i j => ?_⟩
  · exact (congrArg (fun g => β * g * β⁻¹) hY).trans (conj_back _ _)
  · rw [RingHom.map_add]
    exact hY1 i j

variable {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

theorem red_at {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP) {j n : ℕ} (hr : D.R.r ≤ n)
    {e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin n} (he : IsOrd zPos e) (π : EAf D →+* G.k)
    (h1 : ∀ a, π (toEAf D a) = G.q.pr a) (h3 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, π s ∈ 𝒪[G.k])
    (h4 : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP s = 0 ↔ valuation G.k (π s) < 1)
    (Y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : ∀ a b, ¬ FreeIx G.S.ρ a b → valuation G.k (π (Y.val (e a) (e b)) - (1 : Matrix _ _ G.k) a b) < 1) :
    Formalism.UG.bc (resS D.host.F PP) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, G.Red x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP) Y)) := by
  haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hs := G.hs
  obtain ⟨c1, x, c2⟩ := red_of_pattern G.S (by unfold Ranks.r; omega) hr he (resS D.host.F PP)
    (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) h3 h4 Y hy
  refine ⟨c1, x, fun a b a' b' ha hb z hz => ?_⟩
  have := c2 a b a' b' ha hb (oToS D.host.F D.host.E z) ((Formalism.L2.DIV.resS_oToS PP z).trans hz)
  rwa [show (π.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (oToS D.host.F D.host.E z) =
    (ofSplit G.q).pr (z : D.host.E) from h1 (incA D (z : D.host.E))] at this

end Glob

theorem lev_of_pin : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) τ cG (G : ∀ PP : d.c.Pg, GAt d τ PP.1), d.Base → PinGBy G cG →
    ∀ PP, (G PP).Lev := by
  intro D u d τ cG G hB hP PP j c hc x xk hx hxk
  have hs := (G PP).hs
  have hst := hB.st j (by omega)
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  obtain ⟨a, ha⟩ := hB.com.split
  obtain ⟨e, he, hmv⟩ := (G PP).frame j c hc
  obtain ⟨π, h1, h2, h3, h4⟩ := exists_chart (G PP).q (G PP).idem
  let L := typeFrame (G PP).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j c hc)
  obtain ⟨hyK, hyP⟩ := (pattern_iter _ _ _ (G PP).S (Fin D.R.t) j (L.conj.symm xk)).1 hxk
  have hmap : ∀ M : Matrix (Fin (d.st j).V.rank) (Fin (d.st j).V.rank) (AE D),
      (M.map (toEAf D)).map π = M.map (G PP).q.pr := fun M => Matrix.ext fun _ _ => h1 _
  have hγ : GeneralLinearGroup.map π ((d.st j).β⁻¹ * Lev.finE (d.st j).V ((d.t j)⁻¹ * x * d.t j) * (d.st j).β) =
      reGL e (L.conj.symm xk) := by
    rw [← conj_frame ((G PP).FY j c hc) L e (GeneralLinearGroup.map π (Lev.finE (d.st j).V (d.t j) * (d.st j).β))
      (GeneralLinearGroup.map π (Lev.finE (d.st j).V x)) (L.conj.symm xk) ?_ ?_]
    · rw [MonoidHom.map_mul (Lev.finE (d.st j).V), MonoidHom.map_mul (Lev.finE (d.st j).V), MonoidHom.map_inv, conj_conj, MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
    · have hb : ((d.st j).β.val.map (finEmb D)).map (toEAf D) = (d.st j).β.val := Matrix.ext fun _ _ => toEAf_finEmb _
      refine Eq.trans ?_ (hmv _ hb)
      refine Eq.trans ?_ (hmap _)
      rw [Matrix.map_mul, hb]
      rfl
    · rw [MulEquiv.apply_symm_apply]
      exact (hmap _).trans hx.2
  obtain ⟨Y, hY, hYv, hY1⟩ := exists_int (G PP).q π h2 (d.st j).V hst.selfDual hst.frame (t := d.t j) hx.1 (by
    rw [hγ, mem_KO, ← map_inv]
    rw [mem_KO] at hyK
    exact ⟨fun _ _ => hyK.1 _ _, fun _ _ => hyK.2 _ _⟩)
  have hall : ∀ PP' : d.c.Pg, Formalism.UG.bc (resS D.host.F PP'.1) Y ∈ blockTri (blkOf D.R.r D.R.t) ∧
      ∃ x, (G PP').Red x (upperLeftBlock hr (Formalism.UG.bc (resS D.host.F PP'.1) Y)) := fun PP' => by
    by_cases hne : PP' = PP
    · subst hne
      refine red_at (G PP') hr he π h1 h3 h4 Y fun a b hab => ?_
      have e1 : π (Y.val (e a) (e b)) = (L.conj.symm xk).val a b := by
        rw [hYv]
        refine (congrArg (fun g : GL _ _ => g.val (e a) (e b)) hγ).trans ?_
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply]
      rw [e1]
      exact hyP a b hab
    · have hs' := (G PP').hs
      obtain ⟨e', he', -⟩ := (G PP').frame j c (by omega)
      obtain ⟨π', k1, -, k3, k4⟩ := exists_chart (G PP').q (G PP').idem
      refine red_at (G PP') hr he' π' k1 k3 k4 Y fun a b _ => ?_
      have e1 := congrArg π' (hY1 (e' a) (e' b))
      rw [RingHom.map_mul, k1, pr_other (G PP).q (G PP').q ha PP.2 PP'.2 (fun h => hne (Subtype.ext h)) (G PP).idem (G PP').idem,
        zero_mul, RingHom.map_sub] at e1
      have e2 : π' ((1 : Matrix _ _ (EAf D)) (e' a) (e' b)) = (1 : Matrix _ _ (G PP').k) a b := by
        simp only [one_apply, e'.injective.eq_iff]
        split_ifs
        · exact π'.map_one
        · exact π'.map_zero
      rw [← e2, ← e1, Valuation.map_zero]
      exact zero_lt_one
  change _ ∈ Lev.levG _ _ (d.st j).L
  rw [hL]
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem (hB.t j))
    (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G PP).q.split hx.1)) (hB.t j), ?_⟩
  change Lev.finE (d.st j).V _ ∈ Formalism.L2.DIV.lev _ _ _ _
  refine ⟨Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, ⟨Y, hY⟩, fun PP' hPP' => ?_, fun _ h => absurd h (Finset.notMem_empty _)⟩, ?_⟩
  · rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall ⟨PP', hPP'⟩).1
  · refine (hP.grp _).2 fun PP' => ?_
    change ∃ z, (G PP').Red z (upperLeftBlock hr (redFn _ PP'.1 _))
    rw [← hY, Formalism.L2.DIV.redFn_frGL]
    exact (hall PP').2

end GlobalTheory.LocMod.LevBack
end
