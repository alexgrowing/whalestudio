import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TowerAcr

theorem roots_eq {B : Type} [CommRing B] {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (hln : (l : B) ^ n = 0) (J : Ideal B)
    (hJ : ∀ u ∈ J, u ^ l ∈ Ideal.span {(l : B)}) (x y : ℕ → B) (hx : ∀ m, x (m + 1) ^ l = x m)
    (hy : ∀ m, y (m + 1) ^ l = y m) (hxy : ∀ m, x m - y m ∈ J) : x = y := by
  funext m
  have hB : ∀ a b : B, a - b ∈ J → (l : B) ∣ a ^ l - b ^ l := by
    intro a b hab
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl b (a - b)
    have hab' : b + (a - b) = a := by ring
    rw [hab'] at hr
    have hu := hJ _ hab
    rw [Ideal.mem_span_singleton] at hu
    rw [hr]
    have hrw : b ^ l + (a - b) ^ l + (l : B) * b * (a - b) * r - b ^ l
        = (a - b) ^ l + (l : B) * (b * (a - b) * r) := by ring
    rw [hrw]
    exact dvd_add hu (dvd_mul_right _ _)
  have key : ∀ z : ℕ → B, (∀ m, z (m + 1) ^ l = z m) → ∀ k, z (m + k) ^ (l ^ k) = z m := by
    intro z hz k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, ← Nat.add_assoc, hz, ih]
  have hd : (l : B) ∣ x (m + (n + 1)) ^ l - y (m + (n + 1)) ^ l := hB _ _ (hxy _)
  have hdiv := dvd_sub_pow_of_dvd_sub hd n
  rw [← pow_mul, ← pow_mul, ← pow_succ', key x hx (n + 1), key y hy (n + 1)] at hdiv
  have hz : (l : B) ^ (n + 1) = 0 := by rw [pow_succ, hln, zero_mul]
  rw [hz, zero_dvd_iff, sub_eq_zero] at hdiv
  exact hdiv

theorem pow_mem_map {Λ E : Type} [CommRing Λ] [CommRing E] {l : ℕ} (hl : l.Prime) (h : Λ →+* E) (P : Ideal Λ)
    (hP : ∀ x ∈ P, x ^ l ∈ Ideal.span {(l : Λ)}) : ∀ u ∈ P.map h, u ^ l ∈ Ideal.span {(l : E)} := by
  let K : Ideal E :=
    { carrier := {u | u ^ l ∈ Ideal.span {(l : E)}}
      add_mem' := by
        intro a b ha hb
        obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl a b
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hr]
        exact Ideal.add_mem _ (Ideal.add_mem _ ha hb)
          (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
            (Ideal.mem_span_singleton_self _))))
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        rw [zero_pow hl.ne_zero]
        exact Ideal.zero_mem _
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at ha ⊢
        rw [mul_pow]
        exact Ideal.mul_mem_left _ _ ha }
  have hle : P.map h ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    show (h x) ^ l ∈ Ideal.span {(l : E)}
    have hx' := hP x hx
    rw [Ideal.mem_span_singleton] at hx' ⊢
    obtain ⟨c, hc⟩ := hx'
    exact ⟨h c, by rw [← map_pow, hc, map_mul, map_natCast]⟩
  intro u hu
  exact hle hu

theorem nil_of {E : Type} [CommRing E] {l n : ℕ} (hln : (l : E) ^ n = 0) (J : Ideal E)
    (hJ : ∀ u ∈ J, u ^ l ∈ Ideal.span {(l : E)}) : ∀ u ∈ J, IsNilpotent u := by
  intro u hu
  have hu' := hJ u hu
  rw [Ideal.mem_span_singleton] at hu'
  obtain ⟨c, hc⟩ := hu'
  exact ⟨l * n, by rw [pow_mul, hc, mul_pow, hln, zero_mul]⟩

theorem finish {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] {a : O →+* R} {d : ℕ} {T : Fin d → R}
    {I : Ideal Λ} {κ : O →+* Λ ⧸ I} (𝓛 : Lift a T Λ I κ) {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0)
    (X : RootExt l 𝓛.D 𝓛.t) (J : Ideal X.E) (hln : (l : X.E) ^ n = 0)
    (hJ : ∀ u ∈ J, u ^ l ∈ Ideal.span {(l : X.E)}) (hIJ : ∀ x ∈ I, algebraMap 𝓛.D X.E (𝓛.i x) ∈ J)
    (g' : R →+* X.E ⧸ J)
    (hg' : ∀ r z, Ideal.Quotient.mk (I.map 𝓛.i) z = 𝓛.j r → Ideal.Quotient.mk J (algebraMap 𝓛.D X.E z) = g' r)
    {P : Type} [CommRing P] (φ : 𝓛.D →+* P) (e' : P →+* X.E) (τ : Fin d → ℕ → P)
    (hτ : ∀ k m, τ k (m + 1) ^ l = τ k m) (h0 : ∀ k, φ (𝓛.t k) = τ k 0)
    (hi : ∀ x, e' (φ (𝓛.i x)) = algebraMap 𝓛.D X.E (𝓛.i x)) (hr : ∀ k m, e' (τ k m) - X.r k m ∈ J)
    (hD : ∀ r z, Ideal.Quotient.mk (I.map 𝓛.i) z = 𝓛.j r → Ideal.Quotient.mk J (e' (φ z)) = g' r)
    (e : X.E →+* P) (he : ∀ z, e (algebraMap 𝓛.D X.E z) = φ z) (her : ∀ k m, e (X.r k m) = τ k m) :
    ∀ x, e' (e x) = x := by
  have hroot : ∀ k m, e' (τ k m) = X.r k m := by
    intro k m
    have h := roots_eq hl hn hln J hJ (fun m => e' (τ k m)) (fun m => X.r k m)
      (fun m => by show e' (τ k (m + 1)) ^ l = e' (τ k m); rw [← map_pow, hτ])
      (fun m => X.r_succ k m) (fun m => hr k m)
    exact congrFun h m
  have hmod : ∀ z, Ideal.Quotient.mk J (e' (φ z)) = Ideal.Quotient.mk J (algebraMap 𝓛.D X.E z) := by
    have hh : ∀ x ∈ I, ((Ideal.Quotient.mk J).comp ((algebraMap 𝓛.D X.E).comp 𝓛.i)) x = 0 := by
      intro x hx
      simp only [RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ x hx)
    have hg : ∀ o x, Ideal.Quotient.mk I x = κ o →
        g' (a o) = ((Ideal.Quotient.mk J).comp ((algebraMap 𝓛.D X.E).comp 𝓛.i)) x := by
      intro o x hx
      simp only [RingHom.comp_apply]
      exact (hg' (a o) (𝓛.i x) (𝓛.hj o x hx).symm).symm
    obtain ⟨f, -, huniq⟩ := 𝓛.univ (X.E ⧸ J) ((Ideal.Quotient.mk J).comp ((algebraMap 𝓛.D X.E).comp 𝓛.i)) g' hh hg
    have e1 := huniq ((Ideal.Quotient.mk J).comp (e'.comp φ))
      ⟨RingHom.ext fun x => by simp only [RingHom.comp_apply]; rw [hi], fun r z hz => hD r z hz⟩
    have e2 := huniq ((Ideal.Quotient.mk J).comp (algebraMap 𝓛.D X.E))
      ⟨RingHom.ext fun x => by simp only [RingHom.comp_apply], fun r z hz => hg' r z hz⟩
    intro z
    exact RingHom.congr_fun (e1.trans e2.symm) z
  have hφ : e'.comp φ = algebraMap 𝓛.D X.E := by
    letI : Algebra (MvPolynomial (Fin d) Λ) 𝓛.D := (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t).toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) 𝓛.D := 𝓛.et
    letI : Algebra (MvPolynomial (Fin d) Λ) X.E :=
      ((algebraMap 𝓛.D X.E).comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t)).toAlgebra
    have hcomp : (e'.comp φ).comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t)
        = (algebraMap 𝓛.D X.E).comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact hi c
      · intro k
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        rw [h0, hroot, X.r_zero]
    let h₁ : 𝓛.D →ₐ[MvPolynomial (Fin d) Λ] X.E :=
      { toRingHom := e'.comp φ, commutes' := fun q => RingHom.congr_fun hcomp q }
    let h₂ : 𝓛.D →ₐ[MvPolynomial (Fin d) Λ] X.E :=
      { toRingHom := algebraMap 𝓛.D X.E, commutes' := fun q => rfl }
    have h12 := GlobalTheory.CompanionTheory.EtNil.lift_unique J (nil_of hln J hJ) h₁ h₂ (fun z => hmod z)
    exact congrArg AlgHom.toRingHom h12
  have hid : e'.comp e = RingHom.id X.E := by
    obtain ⟨g, -, huniq⟩ := X.univ X.E (algebraMap 𝓛.D X.E) X.r X.r_zero X.r_succ
    have e1 := huniq (e'.comp e) ⟨RingHom.ext fun z => by
        simp only [RingHom.comp_apply]; rw [he]; exact RingHom.congr_fun hφ z,
      fun k m => by simp only [RingHom.comp_apply]; rw [her, hroot]⟩
    have e2 := huniq (RingHom.id X.E) ⟨RingHom.ext fun z => rfl, fun k m => rfl⟩
    exact e1.trans e2.symm
  intro x
  exact RingHom.congr_fun hid x

end GlobalTheory.CompanionTheory.TowerAcr

namespace GlobalTheory.CompanionTheory.TowerAcr

theorem toAcr_sub_mem {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (w : Ainf l) :
    A.toAcr n (A.sW w) - A.toAcr n (WittVector.teichmuller l (A.s (w.coeff 0))) ∈ A.PFil n := by
  rcases subsingleton_or_nontrivial A.A with hA | hA
  · have hs : A.sW w = WittVector.teichmuller l (A.s (w.coeff 0)) :=
      WittVector.ext fun i => Subsingleton.elim _ _
    rw [hs, sub_self]
    exact Ideal.zero_mem _
  · have hl0 : ((l : ℕ) : A.A) = 0 := by
      rw [← map_natCast A.s l, CharP.cast_eq_zero, map_zero]
    haveI : CharP A.A l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).mpr hl0
    obtain ⟨π, hπ, -, -, -⟩ := (GlobalTheory.T.period_ring_base_change_from_universal A n).1
    have hlP : ((l : ℕ) : A.Acr n) ∈ A.PFil n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← map_natCast π l, hl0, map_zero]
    obtain ⟨y, hy⟩ : ∃ y : WittVector l A.A, y = A.sW w - WittVector.teichmuller l (A.s (w.coeff 0)) :=
      ⟨_, rfl⟩
    have hx0 : (A.sW w).coeff 0 = A.s (w.coeff 0) := WittVector.map_coeff A.s w 0
    have hy0 : y.coeff 0 = 0 := by
      have h1 : WittVector.constantCoeff y = y.coeff 0 := rfl
      rw [← h1, hy, map_sub]
      show (A.sW w).coeff 0 - (WittVector.teichmuller l (A.s (w.coeff 0))).coeff 0 = 0
      rw [hx0, WittVector.teichmuller_coeff_zero, sub_self]
    have hV : WittVector.verschiebung (y.shift 1) = y := by
      have h : WittVector.verschiebung (y.shift 1) = y.shift 0 :=
        WittVector.verschiebung_shift y 0 (fun i hi => by
          have hi0 : i = 0 := by omega
          subst hi0
          exact hy0)
      rw [h]
      ext i
      simp [WittVector.shift_coeff]
    obtain ⟨u, hu⟩ := (WittVector.frobenius_bijective l A.A).2 (y.shift 1)
    have hyu : y = u * (l : WittVector l A.A) := by
      rw [← hV, ← hu, WittVector.verschiebung_frobenius]
    rw [← map_sub, ← hy, hyu, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ hlP

theorem map_map {G : CommRingCat.{0} ⥤ Type} {B₀ B₁ B₂ : Type} [CommRing B₀] [CommRing B₁] [CommRing B₂]
    (f : B₀ →+* B₁) (g : B₁ →+* B₂) (y : G.obj (CommRingCat.of B₀)) :
    G.map (CommRingCat.ofHom g) (G.map (CommRingCat.ofHom f) y) = G.map (CommRingCat.ofHom (g.comp f)) y := by
  rw [CommRingCat.ofHom_comp, Functor.map_comp_apply]

theorem pt_eq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}
    (𝒯 : Tower κ s) (k : Bool) (n : ℕ)
    (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n))
    (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0)
    (hn : IsNilpotent ((bs l k n).p : (bs l k n).R))
    (θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj) (r : s.R) :
    Ideal.quotientMap (JJ k 𝒯.A n) θ.φ θ.hle (𝓛.j r) = uJ k 𝒯.A n (𝒯.g r) := by
  have h2 : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap (JJ k 𝒯.A n) θ.φ θ.hle))
      (F.Pt.map (CommRingCat.ofHom 𝓛.j) s.y₀) =
      F.Pt.map (CommRingCat.ofHom (uJ k 𝒯.A n)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) :=
    congrArg (fun z => (Subtype.val z).2) θ.pt
  have h3 := (map_map (G := F.Pt) 𝓛.j (Ideal.quotientMap (JJ k 𝒯.A n) θ.φ θ.hle) s.y₀).symm.trans
    (h2.trans (map_map (G := F.Pt) 𝒯.g (uJ k 𝒯.A n) s.y₀))
  obtain ⟨g0, -, huniq⟩ := s.univ (CommRingCat.of (𝒯.A.Acr n ⧸ JJ k 𝒯.A n))
    (F.Pt.map (CommRingCat.ofHom ((uJ k 𝒯.A n).comp 𝒯.g)) s.y₀) _
    (F.ov_map (CommRingCat.ofHom ((uJ k 𝒯.A n).comp 𝒯.g)) s.ov)
  have e1 := huniq _ h3
  have e2 := huniq ((uJ k 𝒯.A n).comp 𝒯.g) rfl
  exact RingHom.congr_fun (e1.trans e2.symm) r

end GlobalTheory.CompanionTheory.TowerAcr

namespace GlobalTheory.CompanionTheory.TowerAcr

theorem tower_acr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}
    (𝒯 : Tower κ s) (k : Bool) (n : ℕ)
    (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n))
    (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0)
    (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (X : RootExt l 𝓛.D 𝓛.t)
    (θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj) :
    n ≠ 0 → (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) →
    ∃ e : X.E →+* 𝒯.A.Acr n, Function.Bijective e ∧ (∀ z, e (algebraMap 𝓛.D X.E z) = θ.φ z) ∧
      ∀ j m, e (X.r j m) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j m : 𝒯.A.A)) := by
  intro hn0 ht
  have hl : l.Prime := Fact.out
  obtain ⟨⟨πb, hπb, -, hπb0, -⟩, -, -, -, -, hPb, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal (base l) n
  obtain ⟨⟨πA, hπA, -, hπA0, -⟩, -, hJJ, -, -, -, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal 𝒯.A n
  have hPP : 𝒯.A.PFil n = ((base l).PFil n).map (mapAcr 𝒯.A.fromBase n) := hJJ true
  let φ : 𝓛.D →+* 𝒯.A.Acr n := θ.φ
  have hφ : ∀ r, φ (𝓛.i r) = mapAcr 𝒯.A.fromBase n r := θ.comm
  let τ : Fin d → ℕ → 𝒯.A.Acr n := fun j m => 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j m : 𝒯.A.A))
  have hτ : ∀ j m, τ j (m + 1) ^ l = τ j m := fun j m => by
    simp only [τ]
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, 𝒯.c_succ]
  obtain ⟨e, ⟨he0, her⟩, -⟩ := X.univ (𝒯.A.Acr n) φ τ (fun j => (ht j).symm) hτ
  have he : ∀ z, e (algebraMap 𝓛.D X.E z) = φ z := fun z => RingHom.congr_fun he0 z

  let h : (base l).Acr n →+* X.E := (algebraMap 𝓛.D X.E).comp 𝓛.i
  have hh : ∀ x, e (h x) = mapAcr 𝒯.A.fromBase n x := fun x => (he _).trans (hφ x)
  let J : Ideal X.E := ((base l).PFil n).map h
  have hIle : (JJ k (base l) n).map 𝓛.i ≤ J.comap (algebraMap 𝓛.D X.E) :=
    Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_map_of_mem h (le_pfil k (base l) n hx)
  let qJ : 𝓛.D ⧸ (JJ k (base l) n).map 𝓛.i →+* X.E ⧸ J := Ideal.quotientMap J (algebraMap 𝓛.D X.E) hIle
  let g0 : s.R →+* X.E ⧸ J := qJ.comp 𝓛.j
  let qh : (base l).Acr n ⧸ (base l).PFil n →+* X.E ⧸ J := Ideal.quotientMap J h Ideal.le_comap_map
  let o : Ob l →+* X.E ⧸ J := qh.comp πb
  have ho : ∀ a, o a = Ideal.Quotient.mk J (h ((base l).toAcr n (WittVector.teichmuller l a))) := fun a => by
    change qh (πb a) = _
    rw [hπb]; rfl
  have hg0 : ∀ r z, Ideal.Quotient.mk ((JJ k (base l) n).map 𝓛.i) z = 𝓛.j r →
      Ideal.Quotient.mk J (algebraMap 𝓛.D X.E z) = g0 r := fun r z hz => by
    change _ = qJ (𝓛.j r)
    rw [← hz]; rfl
  have hκ : ∀ (x : O) (w : Ainf l), theta0 l w = κ x →
      Ideal.Quotient.mk (JJ k (base l) n) ((base l).toAcr n ((base l).sW w)) = κb κ k n x := fun x w hw => by
    change _ = uJ k (base l) n ((base l).oC (κ x))
    rw [← hw, oC_theta0]; rfl

  obtain ⟨f, ⟨hfs, hfg, hfc⟩, -⟩ := 𝒯.univ (X.E ⧸ J) o g0 (fun j m => Ideal.Quotient.mk J (X.r j m))
    (by change qh (πb (base l).pi) = 0; rw [hπb0, map_zero])
    (fun x w hw => by
      rw [← hg0 _ _ (𝓛.hj x _ (hκ x w hw)).symm, ho]
      refine Ideal.Quotient.eq.2 ?_
      have := Ideal.mem_map_of_mem h (toAcr_sub_mem (base l) n w)
      rw [map_sub] at this
      exact this)
    (fun j => by rw [X.r_zero]; exact hg0 _ _ (𝓛.hT j).symm)
    (fun j m => by rw [← map_pow, X.r_succ])
  obtain ⟨e', he'0, he'f⟩ := (GlobalTheory.T.period_ring_universal_property 𝒯.A n X.E h).1 f fun a => by
    rw [← ho]; exact RingHom.congr_fun hfs a
  have he'm : ∀ x, e' (mapAcr 𝒯.A.fromBase n x) = h x := fun x => RingHom.congr_fun he'0 x

  have hJle : J ≤ (𝒯.A.PFil n).comap e := Ideal.map_le_iff_le_comap.2 fun x hx => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hh, hPP]
    exact Ideal.mem_map_of_mem _ hx
  have hPle : 𝒯.A.PFil n ≤ J.comap e' := by
    rw [hPP]
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, he'm]
    exact Ideal.mem_map_of_mem h hx
  let qe : X.E ⧸ J →+* 𝒯.A.Acr n ⧸ 𝒯.A.PFil n := Ideal.quotientMap _ e hJle
  let qe' : 𝒯.A.Acr n ⧸ 𝒯.A.PFil n →+* X.E ⧸ J := Ideal.quotientMap _ e' hPle
  let fac : 𝒯.A.Acr n ⧸ JJ k 𝒯.A n →+* 𝒯.A.Acr n ⧸ 𝒯.A.PFil n := Ideal.Quotient.factor (le_pfil k 𝒯.A n)
  let uP : 𝒯.A.U →+* 𝒯.A.Acr n ⧸ 𝒯.A.PFil n := fac.comp (uJ k 𝒯.A n)
  have huP : ∀ x, uP (𝒯.A.th x) = Ideal.Quotient.mk _ (𝒯.A.toAcr n x) := fun x => rfl
  have huPl : ∀ u v, u - v ∈ Ideal.span {(l : 𝒯.A.U)} → uP u = uP v := fun u v huv => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 huv
    rw [← sub_eq_zero, ← map_sub, ← hc, map_mul, map_natCast]
    have : ((l : 𝒯.A.Acr n ⧸ 𝒯.A.PFil n)) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (𝒯.A.PFil n))]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
    rw [this, mul_zero]
  have hφg : ∀ r z, Ideal.Quotient.mk ((JJ k (base l) n).map 𝓛.i) z = 𝓛.j r →
      Ideal.Quotient.mk (𝒯.A.PFil n) (φ z) = uP (𝒯.g r) := fun r z hz => by
    have := pt_eq 𝒯 k n 𝓛 δ hδ hp hn θ r
    rw [← hz] at this
    exact congrArg fac this
  have hqg : ∀ r, qe (g0 r) = uP (𝒯.g r) := fun r => by
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
    rw [← hg0 r z hz, ← hφg r z hz]
    change Ideal.Quotient.mk _ (e (algebraMap _ _ z)) = _
    rw [he]
  have hπ : qe.comp f = πA := by
    obtain ⟨f2, -, uniq⟩ := 𝒯.univ (𝒯.A.Acr n ⧸ 𝒯.A.PFil n) (πA.comp 𝒯.A.s) (uP.comp 𝒯.g)
      (fun j m => Ideal.Quotient.mk _ (τ j m)) hπA0
      (fun x w hw => by
        have e1 : 𝒯.g (s.a x) = 𝒯.A.th (𝒯.A.sW w) :=
          (RingHom.congr_fun 𝒯.hg x).trans (by rw [RingHom.comp_apply, ← hw, oC_theta0])
        change uP (𝒯.g (s.a x)) = πA (𝒯.A.s (w.coeff 0))
        rw [e1, huP, hπA]
        exact Ideal.Quotient.eq.2 (toAcr_sub_mem 𝒯.A n w))
      (fun j => by
        change _ = uP (𝒯.g (s.T j))
        rw [← 𝒯.c_sharp]
        exact (huP _).symm)
      (fun j m => by rw [← map_pow, hτ])
    refine (uniq _ ⟨?_, fun r a ha => ?_, fun j m => ?_⟩).trans
      (uniq πA ⟨rfl, fun r a ha => ?_, fun j m => hπA _⟩).symm
    · refine RingHom.ext fun a => ?_
      change qe (f (𝒯.A.s a)) = πA (𝒯.A.s a)
      have h3 : f (𝒯.A.s a) = o a := RingHom.congr_fun hfs a
      rw [h3, ho, hπA]
      change Ideal.Quotient.mk _ (e (h _)) = _
      rw [hh, mapAcr_toAcr, mapW, WittVector.map_teichmuller]
      rfl
    · change qe (f a) = uP (𝒯.g r)
      rw [hfg r a ha, hqg]
    · change qe (f (𝒯.c j m : 𝒯.A.A)) = _
      rw [hfc]
      change Ideal.Quotient.mk _ (e (X.r j m)) = _
      rw [her]
    · change πA a = uP (𝒯.g r)
      rw [hπA, ← huPl _ _ ha]
      exact (huP _).symm
  have h1 : ∀ y, e (e' y) = y := fun y => by
    have h4 := (GlobalTheory.T.period_ring_universal_property 𝒯.A n (𝒯.A.Acr n) (mapAcr 𝒯.A.fromBase n)).2 (e.comp e') (RingHom.id _)
      (RingHom.ext fun x => by rw [RingHom.comp_apply, RingHom.comp_apply, he'm, hh]) (RingHom.id_comp _)
      (fun a => by
        rw [← hPP]
        refine Ideal.Quotient.eq.1 ?_
        have h5 : Ideal.Quotient.mk (𝒯.A.PFil n) (e (e' (𝒯.A.toAcr n (WittVector.teichmuller l a)))) =
            qe (Ideal.Quotient.mk J (e' (𝒯.A.toAcr n (WittVector.teichmuller l a)))) := rfl
        change Ideal.Quotient.mk (𝒯.A.PFil n) (e (e' (𝒯.A.toAcr n (WittVector.teichmuller l a)))) = _
        rw [h5, he'f a]
        exact (RingHom.congr_fun hπ a).trans (hπA a))
    exact RingHom.congr_fun h4 y
  have hln : (l : X.E) ^ n = 0 := by
    rw [← map_natCast h, ← map_pow, (base l).pow_l_acr n, map_zero]
  have h2 : ∀ x, e' (e x) = x := finish 𝓛 hl hn0 X J hln
    (pow_mem_map hl h _ fun x hx => (hPb x hx).2)
    (fun x hx => Ideal.mem_map_of_mem h (le_pfil k (base l) n hx)) g0 hg0 φ e' τ hτ ht
    (fun x => by rw [hφ, he'm]; rfl)
    (fun j m => by
      refine Ideal.Quotient.eq.1 ?_
      rw [he'f, hfc])
    (fun r z hz => by
      obtain ⟨a, ha⟩ := (RL.u_mod 𝒯.A).1 (Ideal.Quotient.mk _ (𝒯.g r))
      rw [sharpMap_eq] at ha
      have ha' : 𝒯.A.sharp a - 𝒯.g r ∈ Ideal.span {(l : 𝒯.A.U)} := by
        have h6 := Ideal.Quotient.eq.1 ha
        rwa [pow_one] at h6
      rw [← hfg r a ha']
      have e2 : Ideal.Quotient.mk J (e' (φ z)) = qe' (Ideal.Quotient.mk _ (φ z)) := rfl
      rw [e2, hφg r z hz, ← huPl _ _ ha', ← he'f a]
      exact congrArg qe' (huP _))
    e he her
  exact ⟨e, Function.bijective_iff_has_inverse.2 ⟨e', h2, h1⟩, he, her⟩

end GlobalTheory.CompanionTheory.TowerAcr
