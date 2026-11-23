import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private theorem l_pfil (A : PAlg l) (n : ℕ) : (l : A.Acr n) ∈ A.PFil n :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

private def tq (A : PAlg l) (n : ℕ) : A.W →+* A.Acr n ⧸ A.PFil n := (Ideal.Quotient.mk _).comp (A.toAcr n)

private theorem tq_l (A : PAlg l) (n : ℕ) : tq A n (l : A.W) = 0 := by
  rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (l_pfil A n)

private theorem tq_xi (A : PAlg l) (n : ℕ) : tq A n A.xi = 0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
  rw [toAcr_xi]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

private theorem xi_coeff (A : PAlg l) : A.xi.coeff 0 = - A.s (pFlat l) := by
  have h : (xi0 l).coeff 0 = - pFlat l := by
    rw [← WittVector.constantCoeff_apply, xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  change (WittVector.map A.s (xi0 l)).coeff 0 = _
  rw [WittVector.map_coeff, h, map_neg]

private def aq (A : PAlg l) (n : ℕ) : A.A →+* A.Acr n ⧸ A.PFil n :=
  (WittVector.constantCoeff (p := l) (R := A.A)).liftOfSurjective (WittVector.constantCoeff_surjective l)
    ⟨tq A n, fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff x).2 hx)
      rw [RingHom.mem_ker, map_mul, tq_l, mul_zero]⟩

private theorem aq_coeff (A : PAlg l) (n : ℕ) (x : A.W) : aq A n (x.coeff 0) = tq A n x :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

private theorem aq_pi (A : PAlg l) (n : ℕ) : aq A n (A.s (pFlat l)) = 0 := by
  have h := aq_coeff A n A.xi
  rw [xi_coeff, map_neg, tq_xi, neg_eq_zero] at h
  exact h

private def qq (A : PAlg l) (n : ℕ) : Qb A →+* A.Acr n ⧸ A.PFil n :=
  Ideal.Quotient.lift _ (aq A n) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, aq_pi, mul_zero]

private theorem qq_mk (A : PAlg l) (n : ℕ) (x : A.W) :
    qq A n (Ideal.Quotient.mk _ (x.coeff 0)) = Ideal.Quotient.mk _ (A.toAcr n x) := aq_coeff A n x

private theorem qq_nat {A A' : PAlg l} (f : A ⟶ A') (n : ℕ) :
    (Ideal.quotientMap (A'.PFil n) (mapAcr f n) (B.jj_le true f n)).comp (qq A n) = (qq A' n).comp (PAlg.mapQ f (pFlat l)) := by
  refine RingHom.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, rfl⟩ := WittVector.constantCoeff_surjective l a
  have e : PAlg.mapQ f (pFlat l) (Ideal.Quotient.mk _ (WittVector.constantCoeff x)) = Ideal.Quotient.mk _ ((mapW f x).coeff 0) := by
    change Ideal.Quotient.mk _ (Hom.f f (x.coeff 0)) = _
    rw [mapW, WittVector.map_coeff]
  rw [RingHom.comp_apply, RingHom.comp_apply, e, qq_mk]
  change Ideal.quotientMap _ _ _ (qq A n (Ideal.Quotient.mk _ (x.coeff 0))) = _
  rw [qq_mk, Ideal.quotientMap_mk, mapAcr_toAcr]

private def iA (r : Res l K) (A : PAlg l) (n : ℕ) : Wc.Wm l r.k n →+* A.Acr n := (mapAcr A.fromBase n).comp (Pb.Mid.wn r n)

private theorem iA_mk (r : Res l K) (A : PAlg l) (n : ℕ) (w : WittVector l r.k) :
    iA r A n (Ideal.Quotient.mk _ w) = A.cris n (r.w w) := mapAcr_cris A.fromBase n (r.w w)

private theorem iA_mk' (r : Res l K) (A : PAlg l) (n : ℕ) (w : WittVector l r.k) :
    iA r A n (Ideal.Quotient.mk _ w) = A.toAcr n (A.sW (WittVector.map r.s w)) :=
  (iA_mk r A n w).trans (A.cris_algebraMap n _)

private theorem iA_nat (r : Res l K) {A A' : PAlg l} (f : A ⟶ A') (n : ℕ) (w : Wc.Wm l r.k n) :
    mapAcr f n (iA r A n w) = iA r A' n w := B.mapAcr_fromBase f n _

private theorem l_pfil0 (A : PAlg l) : (l : A.Acr0) ∈ A.PFil0 :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

private theorem iA_dp (r : Res l K) (A : PAlg l) (n : ℕ) : IsDPMorphism (Wc.pd l r.k n) (A.pdPFil n) (iA r A n) :=
  RL.pd_mor _ _ _ _ _ _ ((algebraMap A.W A.Acr0).comp (A.sW.comp (WittVector.map r.s))) _ Ideal.Quotient.mk_surjective
    (pdI_l l (witt_unit l r.k)) (Wc.isPd l r.k n) (A.isPd_pdPFil n)
    (fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (l_pfil0 A))
    fun x => iA_mk' r A n x

private theorem iA_le (r : Res l K) (A : PAlg l) (n : ℕ) : Wc.Im l r.k n ≤ (A.PFil n).comap (iA r A n) :=
  Ideal.map_le_iff_le_comap.1 (iA_dp r A n).1

private theorem qq_over (r : Res l K) (A : PAlg l) (n : ℕ) :
    (qq A n).comp ((qs A).comp (gRes r)) =
      (Ideal.quotientMap _ (iA r A n) (iA_le r A n)).comp ((Wc.res l r.k n).comp r.ρ) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective l (r.ρ x)
  have e : qs A (gRes r x) = Ideal.Quotient.mk _ ((A.sW (WittVector.map r.s w)).coeff 0) := by
    change Ideal.Quotient.mk _ (A.s (r.s (r.ρ x))) = _
    rw [← hw, sW, WittVector.map_coeff, WittVector.map_coeff]; rfl
  rw [RingHom.comp_apply, RingHom.comp_apply, e, qq_mk, RingHom.comp_apply, RingHom.comp_apply, ← hw, Wc.res_coeff,
    Ideal.quotientMap_mk, iA_mk']

private def phK (A : PAlg l) (n k : ℕ) : A.Acr n →+* A.Acr n := A.phi n ^ k

private theorem phK_succ (A : PAlg l) (n k : ℕ) (x : A.Acr n) : phK A n (k + 1) x = A.phi n (phK A n k x) := by
  rw [phK, pow_succ']; rfl

private theorem phK_zero (A : PAlg l) (n : ℕ) (x : A.Acr n) : phK A n 0 x = x := by
  rw [phK, pow_zero]; rfl

private theorem phK_dp (A : PAlg l) (n k : ℕ) : IsDPMorphism (A.pdPFil n) (A.pdPFil n) (phK A n k) := by
  induction k with
  | zero => exact ⟨by rw [phK, pow_zero]; exact (Ideal.map_id _).le, fun _ _ => rfl⟩
  | succ k ih =>
    have e : phK A n (k + 1) = (A.phi n).comp (phK A n k) := RingHom.ext (phK_succ A n k)
    rw [e]
    exact IsDPMorphism.comp _ (A.dpP_phi n) ih

private theorem phK_cris (A : PAlg l) (n k : ℕ) (a : Acris l) : phK A n k (A.cris n a) = A.cris n (Pb.Mid.phiA l k a) := by
  induction k with
  | zero => rw [phK_zero]; rfl
  | succ k ih => rw [phK_succ, ih, Pb.Mid.phiA_succ, A.phi_cris]

private theorem phK_nat {A A' : PAlg l} (f : A ⟶ A') (n k : ℕ) (x : A.Acr n) : mapAcr f n (phK A n k x) = phK A' n k (mapAcr f n x) := by
  induction k with
  | zero => rw [phK_zero, phK_zero]
  | succ k ih => rw [phK_succ, phK_succ, mapAcr_phi, ih]

private theorem phK_mk (A : PAlg l) (n k : ℕ) (x : A.Acr n) :
    Ideal.Quotient.mk (A.PFil n) (phK A n k x) = Ideal.Quotient.mk (A.PFil n) x ^ l ^ k := by
  induction k with
  | zero => rw [phK_zero, pow_zero, pow_one]
  | succ k ih => rw [phK_succ, B.phi_mk, ih, pow_succ, pow_mul]

private theorem phiA_fix (r : Res l K) (f : ℕ) (hf : ∀ x : r.k, x ^ l ^ f = x) (w : WittVector l r.k) : Pb.Mid.phiA l f (r.w w) = r.w w := by
  have key : ∀ (k : ℕ) (x : Ainf l), ∃ y : Ainf l, Pb.Mid.phiA l k (algebraMap (Ainf l) (Acris l) x) = algebraMap (Ainf l) (Acris l) y ∧
      ∀ i, y.coeff i = x.coeff i ^ l ^ k := by
    intro k x
    induction k with
    | zero => exact ⟨x, rfl, fun i => by simp⟩
    | succ k ih =>
      obtain ⟨y, h1, h2⟩ := ih
      refine ⟨WittVector.frobeniusEquiv l (Ob l) y, ?_, fun i => ?_⟩
      · rw [Pb.Mid.phiA_succ, h1, ACris.phi_algebraMap]
      · rw [WittVector.frobeniusEquiv_coeff, h2, pow_succ, pow_mul]
  obtain ⟨y, h1, h2⟩ := key f (WittVector.map r.s w)
  have e : y = WittVector.map r.s w := by
    ext i
    rw [h2, WittVector.map_coeff, ← map_pow, hf]
  change Pb.Mid.phiA l f (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)) = algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)
  rw [h1, e]

variable (r : Res l K) (M : Model l K) (n : ℕ)

private def gObj (T : El (PQ M.p (gRes r))) : Thick (Wc.L l (B.schFn M.p) r.ρ n) where
  B := T.1.obj.Acr n
  i := iA r T.1.obj n
  J := T.1.obj.PFil n
  δ := T.1.obj.pdPFil n
  adm := ⟨fun _ => ⟨n, T.1.obj.pow_l_acr n⟩, fun h => absurd h (Fact.out : l.Prime).ne_zero⟩
  compat := iA_dp r T.1.obj n
  α := ()
  y := ⟨(Ideal.quotientMap _ (iA r T.1.obj n) (iA_le r T.1.obj n),
      (B.schFn M.p).Pt.map (CommRingCat.ofHom (qq T.1.obj n)) T.2.1), by
    have h := (B.schFn M.p).ov_map (CommRingCat.ofHom (qq T.1.obj n)) (y := T.2.1) (f := (qs T.1.obj).comp (gRes r)) T.2.2
    have e := qq_over r T.1.obj n
    exact e ▸ h⟩
  inα := trivial
  w _ := rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

private def gam : El (PQ M.p (gRes r)) ⥤ Thick (Wc.L l (B.schFn M.p) r.ρ n) where
  obj := gObj r M n
  map {T T'} f := crHom (T := gObj r M n T) (T' := gObj r M n T') (mapAcr f.1.hom n) (iA_nat r f.1.hom n) (B.dd_map true f.1.hom n) fun h => by
    have hy : (B.schFn M.p).Pt.map (CommRingCat.ofHom (PAlg.mapQ f.1.hom (pFlat l))) T.2.1 = T'.2.1 := congrArg Subtype.val f.2
    change (B.schFn M.p).Pt.map (CommRingCat.ofHom (Ideal.quotientMap _ (mapAcr f.1.hom n) h))
      ((B.schFn M.p).Pt.map (CommRingCat.ofHom (qq T.1.obj n)) T.2.1) = (B.schFn M.p).Pt.map (CommRingCat.ofHom (qq T'.1.obj n)) T'.2.1
    rw [← hy]
    refine (Functor.map_comp_apply (B.schFn M.p).Pt (CommRingCat.ofHom (qq T.1.obj n)) _ T.2.1).symm.trans
      (Eq.trans (congrArg (fun g => (B.schFn M.p).Pt.map g T.2.1) ?_)
        (Functor.map_comp_apply (B.schFn M.p).Pt (CommRingCat.ofHom (PAlg.mapQ f.1.hom (pFlat l))) (CommRingCat.ofHom (qq T'.1.obj n)) T.2.1))
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (qq_nat f.1.hom n)
  map_id T := Thick.Hom.ext (RingHom.ext (mapAcr_id n)) (funext fun j => j.elim)
  map_comp f g := Thick.Hom.ext (RingHom.ext (mapAcr_comp f.1.hom g.1.hom n)) (funext fun j => j.elim)

private def gK (k : ℕ) (σ : WittVector l r.k →+* Acris l) (h : ∀ w, Pb.Mid.phiA l k (r.w w) = σ w) :
    CH.Mor (Wc.OM l (B.schFn M.p) r.ρ n) (CH.modF (AcrEl (PQ M.p (gRes r)) n)) σ where
  G := gam r M n
  τ T := { toFun := phK T.1.obj n k
           map_add' := map_add _
           map_smul' := fun w (x : T.1.obj.Acr n) => (map_mul (phK T.1.obj n k) (iA r T.1.obj n (Ideal.Quotient.mk _ w)) x).trans
             (congrArg (· * phK T.1.obj n k x) (by rw [iA_mk, phK_cris, h]; rfl)) }
  nat φ x := (phK_nat φ.1.hom n k x).symm

private theorem phiA_zero (a : Acris l) : Pb.Mid.phiA l 0 a = a := by rw [Pb.Mid.phiA, pow_zero]; rfl

private theorem gK_succ (k : ℕ) (σ : WittVector l r.k →+* Acris l) (h : ∀ w, Pb.Mid.phiA l k (r.w w) = σ w) (j : ℕ)
    (y : CH.H (Wc.OM l (B.schFn M.p) r.ρ n) j) :
    phiH (PQ M.p (gRes r)) n j ((gK r M n k σ h).pull j y) =
      (gK r M n (k + 1) ((ACris.phi ℂ_[l] l).comp σ) fun w => by
        rw [Pb.Mid.phiA_succ, h]; rfl).pull j y := by
  haveI : RingHomCompTriple σ (ACris.phi ℂ_[l] l) ((ACris.phi ℂ_[l] l).comp σ) := ⟨rfl⟩
  change (phiMor (PQ M.p (gRes r)) n).pull j ((gK r M n k σ h).pull j y) = _
  refine (pull_pull ((ACris.phi ℂ_[l] l).comp σ) (gK r M n k σ h) (phiMor (PQ M.p (gRes r)) n) j y).trans ?_
  exact cr_pull_eq ((gK r M n k σ h).comp (σ'' := (ACris.phi ℂ_[l] l).comp σ) (phiMor (PQ M.p (gRes r)) n))
    (gK r M n (k + 1) ((ACris.phi ℂ_[l] l).comp σ) fun w => by rw [Pb.Mid.phiA_succ, h]; rfl) (fun T => 𝟙 (gObj r M n T)) (fun _ _ => rfl)
    (fun (T : El (PQ M.p (gRes r))) x => phK_succ T.1.obj n k x) j y

private theorem phiA_zero' (w : WittVector l r.k) : Pb.Mid.phiA l 0 (r.w w) = r.w w := phiA_zero _

private theorem gK_iter (k : ℕ) (σ : WittVector l r.k →+* Acris l) (h : ∀ w, Pb.Mid.phiA l k (r.w w) = σ w) (j : ℕ)
    (y : CH.H (Wc.OM l (B.schFn M.p) r.ρ n) j) :
    (phiH (PQ M.p (gRes r)) n j)^[k] ((gK r M n 0 r.w (phiA_zero' r)).pull j y) = (gK r M n k σ h).pull j y := by
  induction k generalizing σ with
  | zero =>
    have e : σ = r.w := RingHom.ext fun w => (h w).symm.trans (phiA_zero _)
    subst e
    exact congrFun (Function.iterate_zero _) _
  | succ k ih =>
    have e : σ = (ACris.phi ℂ_[l] l).comp ((Pb.Mid.phiA l k).comp r.w) := RingHom.ext fun w => by
      rw [← h, Pb.Mid.phiA_succ]; rfl
    subst e
    have h' : ∀ w, Pb.Mid.phiA l k (r.w w) = ((Pb.Mid.phiA l k).comp r.w) w := fun w => (RingHom.comp_apply _ _ _).symm
    have i1 := ih _ h'
    exact (Function.iterate_succ_apply' _ _ _).trans ((congrArg _ i1).trans (gK_succ r M n k _ h' j y))

private theorem map_sq' (P : CommRingCat.{0} ⥤ Type) {R S S' T : CommRingCat.{0}} {a : R ⟶ S} {b : S ⟶ T} {c : R ⟶ S'} {d : S' ⟶ T}
    (h : a ≫ b = c ≫ d) (y : P.obj R) : P.map b (P.map a y) = P.map d (P.map c y) :=
  (Functor.map_comp_apply P a b y).symm.trans ((congrArg (fun g => P.map g y) h).trans (Functor.map_comp_apply P c d y))

private theorem l_qb (A : PAlg l) : (l : Qb A) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), A.natCast_l, map_zero]

private theorem l_pq (A : PAlg l) (n : ℕ) : (l : A.Acr n ⧸ A.PFil n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (l_pfil A n)

private def psi (A : PAlg l) (N : ℕ) : A.U →+* Qb A :=
  Ideal.Quotient.lift _ ((Pb.Mid.frbN (l_qb A) N).comp ((Ideal.Quotient.mk _).comp (WittVector.constantCoeff (p := l) (R := A.A)))) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have e : (Ideal.Quotient.mk (Ideal.span {A.s (pFlat l)})) (WittVector.constantCoeff A.xi) = 0 := by
      rw [WittVector.constantCoeff_apply, xi_coeff, map_neg, neg_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [map_mul, RingHom.comp_apply _ _ A.xi, RingHom.comp_apply _ _ A.xi, e, map_zero, mul_zero]

private theorem psi_th (A : PAlg l) (N : ℕ) (x : A.W) : psi A N (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ N :=
  Pb.Mid.frbN_apply _ N _

private theorem qq_psi (A : PAlg l) (n N : ℕ) :
    (CommRingCat.ofHom (B.uJ true A n)) ≫ CommRingCat.ofHom (Pb.Mid.frbN (l_pq A n) N) =
      CommRingCat.ofHom (psi A N) ≫ CommRingCat.ofHom (qq A n) := by
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg CommRingCat.ofHom (RingHom.ext fun x => ?_)
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Pb.Mid.frbN (l_pq A n) N (B.uJ true A n (A.th w)) = qq A n (psi A N (A.th w))
  rw [Pb.Mid.frbN_apply, psi_th, map_pow, qq_mk, B.uJ_th]
  rfl

private theorem qq_frob (A : PAlg l) (n f : ℕ) (h) :
    CommRingCat.ofHom (qq A n) ≫ CommRingCat.ofHom (Ideal.quotientMap (A.PFil n) (phK A n f) h) =
      CommRingCat.ofHom (Pb.Mid.frbN (l_qb A) f) ≫ CommRingCat.ofHom (qq A n) := by
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg CommRingCat.ofHom (RingHom.ext fun q => ?_)
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (qq A n q)
  rw [RingHom.comp_apply, RingHom.comp_apply, Pb.Mid.frbN_apply, map_pow, ← hz, Ideal.quotientMap_mk, phK_mk]

private theorem phK_iA (A : PAlg l) (f : ℕ) (hf : ∀ x : r.k, x ^ l ^ f = x) (w : Wc.Wm l r.k n) : phK A n f (iA r A n w) = iA r A n w := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [iA_mk, phK_cris, phiA_fix r f hf]

private theorem absCl_fr (f : ℕ) (hf : ∀ x : r.k, x ^ l ^ f = x) (F : PQ M.p (gRes r) ⟶ PQ M.p (gRes r)) (hF : IsFr f F) (j : ℕ)
    (y : CH.H (Wc.OM l (B.schFn M.p) r.ρ n) j) :
    (phiH _ n j)^[f] ((gK r M n 0 r.w (phiA_zero' r)).pull j y) = pullH F n j ((gK r M n 0 r.w (phiA_zero' r)).pull j y) := by
  refine (gK_iter r M n f r.w (phiA_fix r f hf) j y).trans ?_
  refine Eq.trans ?_ (pull_pull r.w (gK r M n 0 r.w (phiA_zero' r)) (pullMor F n) j y).symm
  exact cr_pull_eq (gK r M n f r.w (phiA_fix r f hf)) ((gK r M n 0 r.w (phiA_zero' r)).comp (σ'' := r.w) (pullMor F n))
    (fun T => crHom (T := gObj r M n T) (T' := gObj r M n ((elMap F).obj T)) (phK T.1.obj n f) (phK_iA r n T.1.obj f hf)
      (phK_dp T.1.obj n f) fun h => by
        have hy := hF T.1.obj (Pb.Mid.frbN (l_qb T.1.obj) f) (Pb.Mid.frbN_apply _ f) T.2
        change (B.schFn M.p).Pt.map (CommRingCat.ofHom (Ideal.quotientMap _ (phK T.1.obj n f) h))
          ((B.schFn M.p).Pt.map (CommRingCat.ofHom (qq T.1.obj n)) T.2.1) =
            (B.schFn M.p).Pt.map (CommRingCat.ofHom (qq T.1.obj n)) (F.app T.1.obj T.2).1
        rw [hy]
        exact map_sq' (B.schFn M.p).Pt (qq_frob T.1.obj n f h) T.2.1)
    (fun {T T'} g x => (phK_nat g.1.hom n f x).symm)
    (fun (T : El (PQ M.p (gRes r))) x => phK_zero T.1.obj n _) j y

private theorem absCl_rd (N : ℕ) (ρ : M.P ⟶ PQ M.p (gRes r)) (hρ : IsRd N ρ) (m : MuMor r M n) (hm : IsMu r M n N m) (j : ℕ)
    (y : CH.H (Wc.OM l (B.schFn M.p) r.ρ n) j) :
    betaM M n j (m.pull j y) = pullH ρ n j ((gK r M n 0 r.w (phiA_zero' r)).pull j y) := by
  obtain ⟨η, h1, h2, -, h3, h4⟩ := hm
  refine (pull_pull r.w m (B.βMor (B.schFn M.p) (okToOC l K) true n) j y).trans
    (Eq.trans ?_ (pull_pull r.w (gK r M n 0 r.w (phiA_zero' r)) (pullMor ρ n) j y).symm)
  exact cr_pull_eq (m.comp (σ'' := r.w) (B.βMor (B.schFn M.p) (okToOC l K) true n))
    ((gK r M n 0 r.w (phiA_zero' r)).comp (σ'' := r.w) (pullMor ρ n))
    (fun T => crHom (T := m.G.obj ((B.gT (B.schFn M.p) (okToOC l K) true n).obj T)) (T' := gObj r M n ((elMap ρ).obj T))
      (η _).toRingHom (fun w => h3 _ w) (h2 _) fun h => by
        have hy := hρ T.1.obj (psi T.1.obj N) (psi_th _ N) T.2
        refine (h4 ((B.gT (B.schFn M.p) (okToOC l K) true n).obj T) h (Pb.Mid.frbN (l_pq T.1.obj n) N) (Pb.Mid.frbN_apply _ N)).trans ?_
        change (B.schFn M.p).Pt.map (CommRingCat.ofHom (Pb.Mid.frbN (l_pq T.1.obj n) N))
          ((B.schFn M.p).Pt.map (CommRingCat.ofHom (B.uJ true T.1.obj n)) T.2.1) =
            (B.schFn M.p).Pt.map (CommRingCat.ofHom (qq T.1.obj n)) (ρ.app T.1.obj T.2).1
        rw [hy]
        exact map_sq' (B.schFn M.p).Pt (qq_psi T.1.obj n N) T.2.1)
    (fun {T T'} g x => by
      have e := m.nat ((B.gT (B.schFn M.p) (okToOC l K) true n).map g) x
      exact (h1 _ _).symm.trans (e.trans (congrArg (mapAcr g.1.hom n) (h1 _ x))))
    (fun (T : El M.P) x => (phK_zero T.1.obj n _).trans (h1 _ x).symm) j y

theorem absCl : AbsCl := by
  intro l _ K r M f N n j hf F ρ hF hρ m hm y
  exact ⟨(gK r M n 0 r.w (phiA_zero' r)).pull j y, absCl_fr r M n f hf F hF j y, absCl_rd r M n N ρ hρ m hm j y⟩

end UpperTheory.Ru.crystallineComparison
