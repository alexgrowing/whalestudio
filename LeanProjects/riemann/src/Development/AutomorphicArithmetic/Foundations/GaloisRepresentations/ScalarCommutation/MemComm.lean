import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.MemFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TyFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfCen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfIdem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulCen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSphComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CLocEqOneOfNotOverPair

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw IsCen SameK)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem conv_smul_right {X : Type} [Group X] (K : Subgroup X) (f y : X → ℂ) (b : ℂ) :
    conv K f (b • y) = b • conv K f y := by
  funext g
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [← smul_eq_mul, smul_finsum]
  exact finsum_congr fun x => by simp only [smul_eq_mul]; ring

private theorem conv_smul_left {X : Type} [Group X] (K : Subgroup X) (x y : X → ℂ) (a : ℂ) :
    conv K (a • x) y = a • conv K x y := by
  funext g
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [← smul_eq_mul, smul_finsum]
  exact finsum_congr fun x => by simp only [smul_eq_mul]; ring

private theorem comm_of_scaled {X : Type} [Group X] (K : Subgroup X) (hK : IsCommensurated K) (hR : ConvRing)
    {e f f' x y : X → ℂ} {a b : ℂ} (he : e ∈ Hecke ℂ K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K)
    (hx : x ∈ Hecke ℂ K) (hy : y ∈ Hecke ℂ K) (hex : conv K e x = x) (hey : conv K e y = y)
    (h1 : conv K f e = a • x) (h2 : conv K f' e = b • y) (hxy : conv K x y = conv K y x) :
    conv K f (conv K f' e) = conv K f' (conv K f e) := by
  have e1 : conv K f y = a • conv K x y := by
    rw [← hey, ← (hR X K hK f hf e he).2 y hy, h1, conv_smul_left, hey]
  have e2 : conv K f' x = b • conv K y x := by
    rw [← hex, ← (hR X K hK f' hf' e he).2 x hx, h2, conv_smul_left, hex]
  rw [h2, h1, conv_smul_right, conv_smul_right, e1, e2, hxy, smul_comm]

private theorem tf_of_mem {X M : Type} [Group X] [Group M] (T : TyLev X M) {h : X} (hh : h ∈ T.K) : T.tf h = T.tf 1 := by
  have e : DoubleCoset.doubleCoset h (T.K : Set X) T.K = DoubleCoset.doubleCoset 1 (T.K : Set X) T.K :=
    DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨h, hh, 1, T.K.one_mem, by simp⟩)
  funext g
  simp only [TyLev.tf, dosetInd, e]

private theorem nat_not_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (hab : a.Coprime b)
    (ha : (a : R) ∈ I) : (b : R) ∉ I := by
  intro hb
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h : (u : R) * a + v * b = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) huv
  exact hI ((Ideal.eq_top_iff_one I).2 (h ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))

private theorem gl_comm_of_scalar {k : Type} [Field k] {n : ℕ} (A B : GL (Fin n) k) (c : k)
    (h : A.val = c • (1 : Matrix (Fin n) (Fin n) k)) : A * B = B * A := by
  apply Units.ext
  simp [Units.val_mul, h]

private theorem tf_facts : TfAdm ∧ TfIdem ∧ TfComm := by
  have hCen : TfCen := pTfCen pAvgK pTfAdm
  have hIdem : TfIdem := pTfIdem pTfAdm hCen
  have hAct : TfAct := pTfAct pAvgK pDosetCosets pTfAdm
  have hMulCen : TfMulCen := pTfMulCen pTfAdm hCen hIdem
  have hMulL : TfMulL := pTfMulL pTfAdm hAct pDosetIff
  have hMulR : TfMulR := pTfMulR pAvgK pTfAdm pDosetIff
  have hLoc : TfLoc := pTfLoc pTfAdm hAct pDosetIff
  exact ⟨pTfAdm, hIdem, pTfComm pTfAdm pConvRing hMulCen hMulL hMulR hLoc⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private theorem cen_comm (F : Frame S) {x : E} {w : Plc E} {z : GUf E n} (hz : IsCen x w z) (g : S.G.GAf) :
    Commute (F.j z) g := by
  obtain ⟨g', rfl⟩ := F.surj g
  show F.j z * F.j g' = F.j g' * F.j z
  rw [← map_mul, ← map_mul, F.j_tr]
  refine (F.tr.j_eq _ _).2 fun u _ => ?_
  rw [map_mul, map_mul]
  by_cases h : SameK x (cj u) w
  · exact gl_comm_of_scalar _ _ _ ((hz u).1 h)
  · rw [(hz u).2 h]; simp

private theorem place_cases {w u : Plc E} (hne : cj w ≠ w) (h : ¬ GlobalTheory.Cong.Apart u w) : u = w ∨ u = cj w := by
  have h' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := not_not.1 h
  exact GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq E w (cj w) u hne (GlobalTheory.DefU.LocRet.under_conjSrc w) h'

private theorem not_sameK_ne {x : E} {w : Plc E} (h : ¬ SameK x (cj w) w) : cj w ≠ w := by
  intro e
  apply h
  rw [e]
  exact fun _ _ => Iff.rfl

private theorem apart_of_primes {w u : Plc E} {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 E) ∈ w.asIdeal)
    (hb : (b : 𝓞 E) ∈ u.asIdeal) : GlobalTheory.Cong.Apart w u := by
  intro h
  have h1 : (b : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap _ (𝓞 E) (b : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simpa using hb
  rw [← h] at h1
  have h2 : algebraMap _ (𝓞 E) (b : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := h1
  exact nat_not_mem w.isPrime.ne_top hab ha (by simpa using h2)

private theorem comp_cj_ofU (w : Plc E) (a b : finU E n)
    (h : comp w (CertificateRingHomMap.ofU a) = comp w (CertificateRingHomMap.ofU b)) : comp (cj w) (CertificateRingHomMap.ofU a) = comp (cj w) (CertificateRingHomMap.ofU b) := by
  have ha := GlobalTheory.LadicPair.cT_cLoc_conjSrc_mul a.1 w
  have hb := GlobalTheory.LadicPair.cT_cLoc_conjSrc_mul b.1 w
  have h' : cLoc w a.1 = cLoc w b.1 := h
  rw [h'] at ha
  have e := (Units.mul_left_inj (cLoc w b.1)).1 (ha.trans hb.symm)
  have e2 := Matrix.map_injective (RingHom.injective _) (Matrix.transpose_injective e)
  exact Units.ext e2

private def Sh {w₀ : Plc E} (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) (Ty : TyLev S.G.GAf (GLw n w₀)) (x : E)
    (h : S.G.GAf) : Prop :=
  ∃ (w : Spl E p) (t : GLw n w.1) (Z : S.G.GAf), h = (L w).loc t * Z ∧ Ty.Cen Z ∧
    (L w).Fact Ty.K (GlobalTheory.LFun.KGL w.1 n) ∧ Ty.L.Apart (L w) ∧ ¬ SameK x (cj w.1) w.1

private theorem sh_comm (F : Frame S) {w₀ : Plc E} {x : E} {L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)}
    {Ty : TyLev S.G.GAf (GLw n w₀)} (hfac : ∀ w, IsFac F w (L w)) {h h' : S.G.GAf} (hh : Sh L Ty x h) (hh' : Sh L Ty x h') :
    conv Ty.K₀ (Ty.tf h) (Ty.tf h') = conv Ty.K₀ (Ty.tf h') (Ty.tf h) := by
  obtain ⟨w, t, Z, rfl, hZ, hf, ha, hs⟩ := hh
  obtain ⟨w', t', Z', rfl, hZ', hf', ha', hs'⟩ := hh'
  have hC := tf_facts.2.2
  by_cases hap : GlobalTheory.Cong.Apart w'.1 w.1
  · have hLL : (L w).Apart (L w') := by
      constructor
      · intro y
        rw [(hfac w').2, (hfac w).1]
        exact CertificateRingHomMap.comp_loc_of_apart w'.2.1 (Ne.symm hap) y
      · intro y
        rw [(hfac w).2, (hfac w').1]
        exact CertificateRingHomMap.comp_loc_of_apart w.2.1 hap y
    exact (hC _ _ _ _ Ty (L w) _ hf ha Z Z' hZ hZ' t).1 (L w') t' ha' hLL
  · rcases place_cases (not_sameK_ne hs) hap with e | e
    · have e' : w' = w := Subtype.ext e
      subst e'
      exact (hC _ _ _ (GLw n w'.1) Ty (L w') _ hf ha Z Z' hZ hZ' t).2 t' (pSphComm E n w'.1 t t')
    · have hloc : (L w').loc t' = (L w).loc (comp w.1 (CertificateRingHomMap.loc w'.2.1 t')) := by
        rw [(hfac w').2, (hfac w).2, F.j_tr]
        refine (F.tr.j_eq _ _).2 fun u _ => ?_
        by_cases hu : GlobalTheory.Cong.Apart u w.1
        · have hu' : GlobalTheory.Cong.Apart u w'.1 := fun e2 => hu (e2.trans (not_not.1 hap))
          rw [CertificateRingHomMap.comp_loc_of_apart w.2.1 hu, CertificateRingHomMap.comp_loc_of_apart w'.2.1 hu']
        · rcases place_cases (not_sameK_ne hs) hu with rfl | rfl
          · rw [CertificateRingHomMap.comp_loc]
          · exact comp_cj_ofU w.1 (CertificateRingHomMap.locF w'.2.1 t') (CertificateRingHomMap.locF w.2.1 _) (CertificateRingHomMap.comp_loc w.2.1 _).symm
      rw [hloc]
      exact (hC _ _ _ (GLw n w.1) Ty (L w) _ hf ha Z Z' hZ hZ' t).2 _ (pSphComm E n w.1 _ _)

theorem memComm : UpperTheory.Gal.Spc.MemComm := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W hAux N hN hStab L hw Ty hTy g g' θ θ' hs hs'
  obtain ⟨hAdm, hIdem, -⟩ := tf_facts
  have hMF := UpperTheory.Gal.Spc.memFn E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W hAux N hN hStab L hw Ty hTy
  have hTF := UpperTheory.Gal.Spc.tyFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W hAux N hN hStab L hw Ty hTy
  have hOff : ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ → conv Ty.K₀ g.fn (Ty.tf 1) ∈ Off2 W L Ty := by
    intro g θ hs
    obtain ⟨-, -, hb⟩ := hMF g θ hs
    rcases hb with ⟨-, -, he⟩ | ⟨hpr, hW, he⟩
    · rw [he]
      exact Submodule.subset_span ⟨1, map_one _, fun w _ => map_one _, rfl⟩
    · rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨g.h⁻¹, by simp [hpr], fun w hw => by simp [hW w hw], rfl⟩)
  have key : ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ → ∃ (a : ℂ) (h : S.G.GAf),
      conv Ty.K₀ g.fn (Ty.tf 1) = a • Ty.tf h ∧ Ty.L.pr h = 1 ∧ (h = 1 ∨ Sh L Ty x h) := by
    intro g θ hs
    obtain ⟨-, -, hb⟩ := hMF g θ hs
    rcases hb with ⟨-, -, he⟩ | ⟨hpr, hW, he⟩
    · exact ⟨1, 1, by rw [he, one_smul], map_one _, Or.inl rfl⟩
    · rcases hs with ⟨-, ⟨k', hk', hlev, -⟩, -, -⟩ | ⟨w, σ, i, B, hfree, hqr, -, htm, -, -⟩
      · have hK : g.h ∈ Ty.K := (hTy.K_iff _).2
          ⟨⟨k', hk', hlev⟩, fun w hw => by rw [hW w hw]; exact one_mem _⟩
        exact ⟨idx g, 1, by rw [he, tf_of_mem Ty (Ty.K.inv_mem hK)], map_one _, Or.inl rfl⟩
      · obtain ⟨-, -, hIsH, -⟩ := htm
        obtain ⟨hw', t, z, -, hcen, hh⟩ := hIsH
        have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Or.inl rfl))
        have hp : (p : 𝓞 E) ∉ w.asIdeal :=
          nat_not_mem w.isPrime.ne_top ((Nat.coprime_primes σ.atp.prime Fact.out).2 σ.atp.ne) hqw
        obtain ⟨wS, hwS⟩ : ∃ wS : Spl E p, wS = ⟨w, hw', hp⟩ := ⟨_, rfl⟩
        have hap : ∀ u ∈ W, GlobalTheory.Cong.Apart wS.1 u.1 := fun u hu => by
          rw [hwS]
          exact apart_of_primes ((Nat.coprime_primes σ.atp.prime hAux.prime).2 hqr) hqw (hAux.half.above u hu)
        have hfr : wS.1 ∉ V.S ∧ cj wS.1 ∉ V.S ∧ ¬ SameK x (cj wS.1) wS.1 := by
          rw [hwS]
          exact ⟨hfree.2.1, hfree.2.2.1, hfree.2.2.2.2⟩
        obtain ⟨hfact, hTap⟩ := hTF.2.1 wS hfr.1 hfr.2.1 hap
        obtain ⟨t₁, ht₁⟩ : ∃ t₁ : GLw n wS.1, (L wS).loc t₁ = F.j (CertificateRingHomMap.loc hw' t) := by
          subst hwS
          exact ⟨t, (hTy.fac ⟨w, hw', hp⟩).2 t⟩
        obtain ⟨C, hCdef⟩ : ∃ C, C = F.j z ^ i := ⟨_, rfl⟩
        have hC : ∀ y, Commute C y := fun y => hCdef ▸ (cen_comm F hcen y).pow_left i
        have hgh : g.h = (L wS).loc t₁ * C := by rw [hh, map_mul, map_pow, ht₁, hCdef]
        have hprC : Ty.L.pr C = 1 := by
          have h1 := hpr
          rw [hgh, map_mul, hTap.1 t₁, one_mul] at h1
          exact h1
        have hinv : g.h⁻¹ = (L wS).loc t₁⁻¹ * C⁻¹ := by
          rw [hgh, map_inv, _root_.mul_inv_rev]
          exact ((hC _).inv_left.inv_right).eq
        exact ⟨idx g, g.h⁻¹, he, by simp [hpr], Or.inr ⟨wS, t₁⁻¹, C⁻¹, hinv,
          ⟨fun y => (hC y).inv_left.eq, by simp [hprC]⟩, hfact, hTap, hfr.2.2⟩⟩
  obtain ⟨a, h, e1, hp, hs1⟩ := key g θ hs
  obtain ⟨b, h', e2, hp', hs2⟩ := key g' θ' hs'
  refine ⟨hOff g θ hs, ?_⟩
  have he : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := (hAdm _ _ Ty 1 (map_one _)).1.1
  refine comm_of_scaled Ty.K₀ Ty.cms pConvRing he (hMF g θ hs).1 (hMF g' θ' hs').1 (hAdm _ _ Ty h hp).1.1
    (hAdm _ _ Ty h' hp').1.1 (hIdem _ _ Ty h hp).2.2 (hIdem _ _ Ty h' hp').2.2 e1 e2 ?_
  rcases hs1 with rfl | hs1
  · rw [(hIdem _ _ Ty h' hp').2.1, (hIdem _ _ Ty h' hp').2.2]
  · rcases hs2 with rfl | hs2
    · rw [(hIdem _ _ Ty h hp).2.1, (hIdem _ _ Ty h hp).2.2]
    · exact sh_comm F hTy.fac hs1 hs2

end UpperTheory.Gal.Spc
