import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueLiftOfNilpotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleRootExt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UZeroApplySelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompletionComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfOfIsCompl

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TowerEx

theorem compl_factor {E S B : Type} [CommRing E] [CommRing S] [CommRing B] {π : E} {g : E →+* S}
    (h : CrystallineSemistableComparison.D.IsCompl π g) (f : E →+* B) (hf : f π = 0) :
    ∃! f' : S →+* B, f'.comp g = f ∧ f' (g π) = 0 := by
  have hle : Ideal.span {π} ≤ (Ideal.span {g π}).comap g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.mem_span_singleton_self _
  let q : E ⧸ Ideal.span {π} →+* S ⧸ Ideal.span {g π} := Ideal.quotientMap _ g hle
  have hqm : ∀ x, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (g x) := fun x => Ideal.quotientMap_mk
  have hinj : Function.Injective q := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hqm, Ideal.Quotient.eq_zero_iff_mem] at hx
    have := h.inj 1 x (by simpa using hx)
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using this)
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := h.surj 1 y
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [hqm]
    exact (Ideal.Quotient.eq.2 (by simpa using hx)).symm
  let e := RingEquiv.ofBijective q ⟨hinj, hsurj⟩
  have hkill : ∀ a ∈ Ideal.span {π}, f a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hf, mul_zero]
  let f₁ : E ⧸ Ideal.span {π} →+* B := Ideal.Quotient.lift _ f hkill
  have hes : ∀ x, e.symm (Ideal.Quotient.mk _ (g x)) = Ideal.Quotient.mk _ x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    exact (hqm x).symm
  refine ⟨(f₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _), ⟨?_, ?_⟩, ?_⟩
  · ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hes]
    exact Ideal.Quotient.lift_mk _ _ _
  · have : Ideal.Quotient.mk (Ideal.span {g π}) (g π) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    simp only [RingHom.comp_apply, this, map_zero]
  · rintro f' ⟨h1, h2⟩
    have hfx : ∀ x, ((f₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _)) (g x) = f x := fun x => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hes]
      exact Ideal.Quotient.lift_mk _ _ _
    have hz : ((f₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk (Ideal.span {g π}))) (g π) = 0 := by
      rw [hfx, hf]
    ext y
    obtain ⟨x, hx⟩ := h.surj 1 y
    rw [pow_one] at hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
    have hy : y = g x + c * g π := by rw [hc]; ring
    rw [hy, map_add, map_add, map_mul, map_mul, h2, hz, mul_zero, mul_zero, add_zero, add_zero, hfx]
    exact RingHom.congr_fun h1 x

theorem isUnit_of_complete {S : Type} [CommRing S] {ϖ : S} (hc : IsAdicComplete (Ideal.span {ϖ}) S) {x : S}
    (h : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ}) x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h.exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  have h1 : x * u - 1 ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq, map_mul, hu, map_one]
  have h2 := IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ}) h1
  have h3 := Ideal.mem_jacobson_bot.1 h2 1
  have h4 : IsUnit (x * u) := by simpa using h3
  exact isUnit_of_mul_isUnit_left h4

theorem exists_factor {O Λ V : Type} [CommRing O] [CommRing Λ] [CommRing V] (q : Λ →+* V)
    (hq : Function.Surjective q) (I : Ideal Λ) (hI : RingHom.ker q = I) (φ : O →+* V) :
    ∃ κf : O →+* Λ ⧸ I, ∀ o x, Ideal.Quotient.mk I x = κf o ↔ q x = φ o := by
  subst hI
  let e := RingHom.quotientKerEquivOfSurjective hq
  refine ⟨e.symm.toRingHom.comp φ, fun o x => ?_⟩
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [RingEquiv.eq_symm_apply]
  exact Iff.rfl

theorem core {p : ℕ} (hp : p ≠ 0) {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] {a : O →+* R} {d : ℕ}
    {T : Fin d → Rˣ} (het : (MvPolynomial.eval₂Hom a fun k => (T k : R)).Etale)
    {π : Λ} {κf : O →+* Λ ⧸ Ideal.span {π}} (L : Lift a (fun k => (T k : R)) Λ (Ideal.span {π}) κf)
    (X : RootExt p L.D L.t) {S : Type} [CommRing S] {g : X.E →+* S}
    (hc : CrystallineSemistableComparison.D.IsCompl (algebraMap L.D X.E (L.i π)) g)
    {U : Type} [CommRing U] {J : Ideal U} (hJ : EtLift J)
    (aq : S →+* U ⧸ J) (hker : RingHom.ker aq = Ideal.span {g (algebraMap L.D X.E (L.i π))})
    (sh : S → U) (hsh : ∀ z, aq z = Ideal.Quotient.mk J (sh z))
    (oc : O →+* U) (hoc : ∀ o x, Ideal.Quotient.mk (Ideal.span {π}) x = κf o →
      aq (g (algebraMap L.D X.E (L.i x))) = Ideal.Quotient.mk J (oc o)) :
    ∃ (c : Fin d → ℕ → Sˣ) (gT : R →+* U), (∀ k m, c k (m + 1) ^ p = c k m) ∧ gT.comp a = oc ∧
      (∀ k, sh (c k 0) = gT (T k)) ∧
      ∀ (B : Type) [CommRing B] (o : Λ →+* B) (g' : R →+* B) (ρ : Fin d → ℕ → B), o π = 0 →
        (∀ o' x, Ideal.Quotient.mk (Ideal.span {π}) x = κf o' → g' (a o') = o x) →
        (∀ k, ρ k 0 = g' (T k)) → (∀ k m, ρ k (m + 1) ^ p = ρ k m) →
        ∃! f : S →+* B, f.comp ((g.comp (algebraMap L.D X.E)).comp L.i) = o ∧
          (∀ r z, sh z - gT r ∈ J → f z = g' r) ∧ ∀ k m, f (c k m) = ρ k m := by
  set gD : L.D →+* S := g.comp (algebraMap L.D X.E) with hgD
  have hgDa : ∀ z, gD z = g (algebraMap L.D X.E z) := fun _ => rfl
  set ϖ : S := g (algebraMap L.D X.E (L.i π)) with hϖ
  have hϖD : gD (L.i π) = ϖ := rfl
  have hIm : (Ideal.span {π}).map L.i = Ideal.span {L.i π} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hle : (Ideal.span {π}).map L.i ≤ (Ideal.span {ϖ}).comap gD := by
    rw [hIm, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hϖD]
    exact Ideal.mem_span_singleton_self _
  have hu0 : ∀ k, IsUnit (g (X.r k 0)) := by
    intro k
    have h1 : IsUnit (Ideal.Quotient.mk ((Ideal.span {π}).map L.i) (L.t k)) := by
      rw [← L.hT k]
      exact (T k).isUnit.map L.j
    have h2 := h1.map (Ideal.quotientMap _ gD hle)
    rw [Ideal.quotientMap_mk] at h2
    rw [X.r_zero k]
    exact isUnit_of_complete hc.compl h2
  have hpow : ∀ k m, g (X.r k m) ^ p ^ m = g (X.r k 0) := by
    intro k m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', pow_mul, ← map_pow, X.r_succ, ih]
  have hu : ∀ k m, IsUnit (g (X.r k m)) := fun k m => by
    have := hu0 k
    rw [← hpow k m] at this
    exact (isUnit_pow_iff (pow_ne_zero m hp)).1 this
  choose c hcv using fun k m => (hu k m)
  have hker0 : ∀ z ∈ (Ideal.span {π}).map L.i, (aq.comp gD) z = 0 := by
    intro z hz
    have h1 := hle hz
    rw [Ideal.mem_comap] at h1
    have h2 : gD z ∈ RingHom.ker aq := by rw [hker]; exact h1
    exact h2
  let lf : L.D ⧸ (Ideal.span {π}).map L.i →+* U ⧸ J := Ideal.Quotient.lift _ (aq.comp gD) hker0
  have hlf : ∀ z, lf (Ideal.Quotient.mk _ z) = aq (gD z) := fun z => Ideal.Quotient.lift_mk _ _ _
  let f0 : MvPolynomial (Fin d) O →+* U := MvPolynomial.eval₂Hom oc fun k => sh (c k 0)
  let g0 : R →+* U ⧸ J := lf.comp L.j
  have hcomp : g0.comp (MvPolynomial.eval₂Hom a fun k => (T k : R)) = (Ideal.Quotient.mk J).comp f0 := by
    apply MvPolynomial.ringHom_ext
    · intro o
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κf o)
      simp only [RingHom.comp_apply, f0, g0, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [L.hj o x hx, hlf]
      exact hoc o x hx
    · intro k
      simp only [RingHom.comp_apply, f0, g0, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [L.hT k, hlf, ← hsh, hcv k 0, X.r_zero k]
      rfl
  obtain ⟨gT, ⟨h1, h2⟩, -⟩ := hJ _ _ _ het f0 g0 hcomp
  have hmkT : ∀ r, Ideal.Quotient.mk J (gT r) = lf (L.j r) := fun r => RingHom.congr_fun h2 r
  have key : ∀ z r, Ideal.Quotient.mk ((Ideal.span {π}).map L.i) z = L.j r →
      aq (gD z) = Ideal.Quotient.mk J (gT r) := fun z r h => by
    rw [hmkT, ← h, hlf]
  refine ⟨c, gT, ?_, ?_, ?_, ?_⟩
  · intro k m
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hcv, hcv, ← map_pow, X.r_succ]
  · ext o
    have := RingHom.congr_fun h1 (MvPolynomial.C o)
    simpa [f0] using this
  · intro k
    have := RingHom.congr_fun h1 (MvPolynomial.X k)
    simpa [f0] using this.symm
  intro B _ o g' ρ ho hcp h0 hs
  have hkill : ∀ x ∈ Ideal.span {π}, o x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, ho, mul_zero]
  obtain ⟨fD, ⟨hD1, hD2⟩, hDu⟩ := L.univ B o g' hkill hcp
  have hDt : ∀ k, ρ k 0 = fD (L.t k) := fun k => by
    rw [h0, hD2 (T k) (L.t k) (L.hT k).symm]
  obtain ⟨fE, ⟨hE1, hE2⟩, hEu⟩ := X.univ B fD ρ hDt hs
  have hEa : ∀ z, fE (algebraMap L.D X.E z) = fD z := fun z => RingHom.congr_fun hE1 z
  have hDi : ∀ x, fD (L.i x) = o x := fun x => RingHom.congr_fun hD1 x
  have hEπ : fE (algebraMap L.D X.E (L.i π)) = 0 := by rw [hEa, hDi, ho]
  obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := compl_factor hc fE hEπ
  have hfg : ∀ z, f (g z) = fE z := fun z => RingHom.congr_fun hf1 z
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · ext x
    simp only [RingHom.comp_apply, hgD, hfg, hEa, hDi]
  · intro r z hz
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (L.j r)
    have e1 : aq z = aq (gD w) := by
      rw [key w r hw, hsh]
      exact Ideal.Quotient.eq.2 hz
    have e2 : z - gD w ∈ Ideal.span {ϖ} := by
      rw [← hker, RingHom.mem_ker, map_sub, e1, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 e2
    have e3 : z = gD w + y * ϖ := by rw [hy]; ring
    rw [e3, map_add, map_mul, hf2, mul_zero, add_zero, hgDa, hfg, hEa]
    exact hD2 r w hw
  · intro k m
    rw [hcv, hfg, hE2]
  · rintro f' ⟨k1, k2, k3⟩
    have k1' : ∀ x, f' (gD (L.i x)) = o x := fun x => RingHom.congr_fun k1 x
    have hD' : (f'.comp gD) = fD := hDu _ ⟨RingHom.ext k1', fun r z hz => by
      refine k2 r (gD z) ?_
      have := key z r hz
      rw [hsh] at this
      exact Ideal.Quotient.eq.1 this⟩
    have hE' : f'.comp g = fE := hEu _ ⟨hD', fun k m => by
      rw [RingHom.comp_apply, ← hcv, k3]⟩
    exact hfu f' ⟨hE', (k1' π).trans ho⟩

variable {l : ℕ} [Fact l.Prime]

theorem mem_span_iff_of_bijective {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (e : R₁ →+* R₂)
    (he : Function.Bijective e) (n : ℕ) (x : R₁) :
    e x ∈ Ideal.span {(n : R₂) ^ 1} ↔ x ∈ Ideal.span {(n : R₁)} := by
  rw [pow_one, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := he.2 y
    refine ⟨y, he.1 ?_⟩
    rw [hy, map_mul, map_natCast]
  · rintro ⟨y, rfl⟩
    exact ⟨e y, by rw [map_mul, map_natCast]⟩

theorem exists_kappa {O : Type} [CommRing O] (κ : O →+* OC l) :
    ∃ κf : O →+* Ob l ⧸ Ideal.span {pFlat l}, ∀ (o : O) (w : Ainf l),
      Ideal.Quotient.mk (Ideal.span {pFlat l}) (w.coeff 0) = κf o ↔ theta0 l w - κ o ∈ Ideal.span {(l : OC l)} := by
  have hb := (RL.base_acr (base l) (isBase_base)).1.2
  have hm := RL.u_mod (base l)
  obtain ⟨κf, hκ⟩ := exists_factor (base l).aToU1 hm.1 (Ideal.span {pFlat l}) hm.2
    ((Ideal.Quotient.mk (Ideal.span {(l : (base l).U) ^ 1})).comp ((base l).oC.comp κ))
  refine ⟨κf, fun o w => ?_⟩
  refine (hκ o (w.coeff 0)).trans ?_
  have h1 : (base l).aToU1 (w.coeff 0) = Ideal.Quotient.mk _ ((base l).oC (theta0 l w)) := by
    have e1 := (base l).sharpMap_coeff w
    have e2 := (base l).oC_theta0 w
    have e3 : (base l).sW w = w := wmap_id w
    rw [e3] at e2
    rw [e2]
    exact e1
  rw [h1, RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq, ← map_sub]
  exact mem_span_iff_of_bijective _ hb l _

theorem aToU1_s_eq_mk_oC_of_theta0_sub_mem (A : PAlg l) (x : Ob l) (y : OC l)
    (h : theta0 l (WittVector.teichmuller l x) - y ∈ Ideal.span {(l : OC l)}) :
    A.aToU1 (A.s x) = Ideal.Quotient.mk _ (A.oC y) := by
  have e1 : A.sharp (A.s x) = A.oC (theta0 l (WittVector.teichmuller l x)) := by
    rw [oC_theta0, sW, WittVector.map_teichmuller]
    rfl
  rw [sharpMap_eq, e1, Ideal.Quotient.eq, ← map_sub, pow_one]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h
  rw [hc, map_mul, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem exists_theta_eq (w : Ainf l) (y : OC l) (h : theta0 l w - y ∈ Ideal.span {(l : OC l)}) :
    ∃ w' : Ainf l, theta0 l w' = y ∧ w'.coeff 0 = w.coeff 0 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨v, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l c
  refine ⟨w - (l : Ainf l) * v, ?_, ?_⟩
  · rw [map_sub, map_mul, map_natCast, ← hc]; ring
  · have hl : (l : Ob l) = 0 := (base l).natCast_l
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, map_natCast, hl, zero_mul, sub_zero,
      WittVector.constantCoeff_apply]

theorem pf_ob : CrystallineSemistableComparison.D.Pf l (Ob l) := ⟨(base l).natCast_l, (base l).perf.bijective_frobenius⟩

theorem tower_ex {O : Type} [CommRing O] {F : Fn O} (κ : O →+* OC l) {d : ℕ} (s : F.Small d) :
    Nonempty (Tower κ s) := by
  have hl : l.Prime := Fact.out
  obtain ⟨κf, hκf⟩ := exists_kappa κ
  obtain ⟨L⟩ := GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift s.a (fun k => (s.T k : s.R)) (Ideal.span {pFlat l}) κf s.et
  obtain ⟨X⟩ := GlobalTheory.CompanionTheory.RootAdjoin.nonempty_rootExt l hl L.D L.t
  have hP := GlobalTheory.CompanionTheory.RootPerf.root_perf l hl L.i L.t L.et pf_ob X
  obtain ⟨S, _, g, hc⟩ := GlobalTheory.CompanionTheory.AdicCompl.exists_isCompl X.E (algebraMap L.D X.E (L.i (pFlat l)))
  have hS : CrystallineSemistableComparison.D.Pf l S := GlobalTheory.CompanionTheory.PerfectRing.pf_of_isCompl l X.E S _ g hc hP.1
  have hnz := GlobalTheory.CompanionTheory.ComplReg.isCompl_nonZeroDivisor X.E S _ g hc (hP.2 _ RL.base_ex.2)
  let A : PAlg l :=
    { A := S, s := (g.comp (algebraMap L.D X.E)).comp L.i, perf := ⟨hS.bij⟩, compl := hc.compl, tf := hnz }
  have hJ : EtLift (Ideal.span {(l : A.U) ^ 1}) :=
    GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete _ (by rw [pow_one]; exact A.completeU)
  obtain ⟨c, gT, h1, h2, h3, h4⟩ := core hl.ne_zero s.et L X hc hJ (S := A.A) A.aToU1 (RL.u_mod A).2 A.sharp A.sharpMap_eq
    (A.oC.comp κ) (fun o x hx => by
      have h := (hκf o (WittVector.teichmuller l x)).1 (by rwa [WittVector.teichmuller_coeff_zero])
      exact aToU1_s_eq_mk_oC_of_theta0_sub_mem A x (κ o) h)
  refine ⟨⟨A, gT, h2, c, h1, h3, ?_⟩⟩
  intro B _ o g' ρ ho hcp h0 hs
  have := h4 B o g' ρ ho (fun o' x hx => by
    have h := (hκf o' (WittVector.teichmuller l x)).1 (by rwa [WittVector.teichmuller_coeff_zero])
    obtain ⟨w', e1, e2⟩ := exists_theta_eq _ _ h
    have e3 := hcp o' w' e1
    rw [e2, WittVector.teichmuller_coeff_zero] at e3
    exact e3) h0 hs
  simp only [pow_one] at this
  exact this

end GlobalTheory.CompanionTheory.TowerEx
