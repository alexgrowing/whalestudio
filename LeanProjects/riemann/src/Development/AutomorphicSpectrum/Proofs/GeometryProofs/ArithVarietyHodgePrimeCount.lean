import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MulMemSqOfSmulEqZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerAtOneCompEndo
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingNoetherianNormalFraction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPointInChartDominated
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpMapEqFromSpecStalk
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunPart

open GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunAlg GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

section Order

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

def augSub (A : Subalgebra R (T → R)) : Submodule R (T → R) where
  carrier := {f | f ∈ A ∧ f 1 = 0}
  add_mem' := fun ha hb => ⟨A.add_mem ha.1 hb.1, by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨A.zero_mem, rfl⟩
  smul_mem' := fun c _ h => ⟨A.smul_mem h.1 c, by simp [h.2]⟩

def toAug {A : Subalgebra R (T → R)} (f : augSub A) : augIdeal A := ⟨⟨f.1, f.2.1⟩, f.2.2⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def augCl (A : Subalgebra R (T → R)) : augSub A →ₗ[R] omega A where
  toFun f := (augIdeal A).toCotangent (toAug f)
  map_add' f g := by
    rw [← LinearMap.map_add]
    rfl
  map_smul' c f := by
    have h : toAug (c • f) = algebraMap R A c • toAug f := rfl
    rw [h, LinearMap.map_smul, algebraMap_smul]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem augCl_surjective (A : Subalgebra R (T → R)) : Function.Surjective (augCl A) := fun x => by
  obtain ⟨f, rfl⟩ := Ideal.toCotangent_surjective _ x
  exact ⟨⟨f.1.1, f.1.2, f.2⟩, rfl⟩

end Order

theorem spec_field_ext {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {Y : Scheme.{0}}
    {v v' : Spec (CommRingCat.of K) ⟶ Y} (h : spMap φ ≫ v = spMap φ ≫ v') : v = v' := by
  refine ext_of_injective φ.injective ?_ h
  let z : Spec (CommRingCat.of K') := IsLocalRing.closedPoint K'
  have e : (spMap φ) z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  have h1 : (spMap φ ≫ v) z = (spMap φ ≫ v') z := by rw [h]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e] at h1
  exact h1

section Tors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {F : Type} [Field F] {N p : ℕ}
  (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}))

variable {pq sc} in
theorem fromN_toN (h : IsSec pq sc) (a : Fin N → F) : fromN pq (toN sc a : TorsT E N p) = a :=
  funext fun i => h.1 _

theorem fromN_one : fromN pq (1 : TorsT E N p) = 0 :=
  funext fun i => by simp [fromN]

theorem toN_zero : (toN sc (0 : Fin N → F) : TorsT E N p) = 1 :=
  Multiplicative.toAdd.injective (funext fun i => by simp [toN])

def idem : TorsT E N p →* TorsT E N p where
  toFun t := toN sc (fromN pq t)
  map_one' := by rw [fromN_one, toN_zero]
  map_mul' s t := Multiplicative.toAdd.injective (funext fun i => by simp [toN, fromN])

variable {pq sc} in

theorem exists_eps (h : IsSec pq sc) : ∃ ε : 𝓞 E, pq (Ideal.Quotient.mk _ ε) = 1 ∧
    ∀ u, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) ε * u = sc (pq u) := by
  obtain ⟨ε, hε⟩ := Ideal.Quotient.mk_surjective (sc 1)
  refine ⟨ε, by rw [hε]; exact h.1 1, fun u => ?_⟩
  rw [hε]
  have h1 := h.2 (u - sc (pq u)) 1 (by simp [h.1])
  have h2 := h.2 (sc 1 - 1) (pq u) (by simp [h.1])
  linear_combination h1 + h2

variable {pq sc} in
theorem idem_qmk {ε : 𝓞 E} (hε : ∀ u, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) ε * u = sc (pq u))
    (x : Fin N → 𝓞 E) : idem pq sc (qmk p x) = qmk p (ε • x) :=
  Multiplicative.toAdd.injective (funext fun i => by
    change sc (pq (Ideal.Quotient.mk _ (x i))) = Ideal.Quotient.mk _ (ε * x i)
    rw [map_mul, hε])

theorem exists_qmk (t : TorsT E N p) : ∃ x, qmk p x = t := by
  choose x hx using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  exact ⟨x, Multiplicative.toAdd.injective (funext hx)⟩

end Tors

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

theorem toLi_rho (P : ChartPack G O c') (a : 𝓞 E) (v : P.L) : P.toLi (P.ρ a v) = 𝔐.ρ a (P.toLi v) := by
  apply 𝔐.M.inj
  apply Over.OverMorphism.ext
  rw [P.toLi_pt, 𝔐.act a (P.toLi v), P.act a v, Over.comp_left, Over.comp_left, P.toLi_pt, Category.assoc]

theorem pts_idem (P : ChartPack G O c') {F : Type} [Field F]
    {pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F} {sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})} {ε : 𝓞 E}
    (hε : ∀ u, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) ε * u = sc (pq u)) (t : TorsT E (D.p + D.q) p) :
    (P.Γ₁.pt (idem pq sc t)).left ≫ P.i₁ = (P.Γ₁.pt t).left ≫ P.i₁ ≫ (𝔐.t.act.act ε).left := by
  obtain ⟨x, rfl⟩ := exists_qmk t
  rw [idem_qmk hε]
  apply spec_field_ext (fracToField (CR O y c'))
  have h1 := P.pts₁ (qmk p (ε • x))
  have h2 := P.pts₁ (qmk p x)
  have h3 := congrArg (fun g => g.left) (G.t₁.lin ε x)
  simp only [Over.comp_left] at h3
  rw [← h1, h3, h2]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in

theorem lat_eq_span [Smooth 𝔐.t.G.hom] (P : ChartPack G O c') (q : Cpt 𝔐.ξ)
    (ψ : CR O y c' →+* 𝔐.X.presheaf.stalk q.1) (h1 : spMap ψ ≫ P.x = 𝔐.X.fromSpecStalk q.1)
    (h2 : (genMap 𝔐.ξ q).comp ψ = algebraMap (CR O y c') Ω) :
    𝔐.M.lat q = Submodule.span (regAt 𝔐.ξ q) (Set.range P.toLi) := by
  obtain ⟨Fq, _, _, ⟨Mq⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G (𝔐.X.presheaf.stalk q.1) (𝔐.X.fromSpecStalk q.1)
  obtain ⟨jq, hjq⟩ := exists_tr (A := 𝔐.X.presheaf.stalk q.1) (𝔐.X.fromSpecStalk q.1) 𝔐.ξ (genMap 𝔐.ξ q)
    (spec_genMap 𝔐.ξ q) Mq 𝔐.M
  obtain ⟨b₀, hb₀⟩ := exists_tr (A := CR O y c') (B := 𝔐.X.presheaf.stalk q.1) P.x (𝔐.X.fromSpecStalk q.1) ψ h1
    P.M Mq
  have hcomp : ∀ e, jq (b₀ e) = P.toLi e := fun e => pt_left_inj 𝔐.M (by
    rw [hjq, hb₀, ← Category.assoc, spMap_dual_comp, h2, P.toLi_pt])
  letI : Algebra (CR O y c') (𝔐.X.presheaf.stalk q.1) := ψ.toAlgebra
  letI : Module (CR O y c') Fq := Module.compHom Fq ψ
  haveI : IsScalarTower (CR O y c') (𝔐.X.presheaf.stalk q.1) Fq :=
    ⟨fun s r e => by
      change (ψ s * r) • e = ψ s • r • e
      rw [mul_smul]⟩
  let b' : P.L →ₗ[CR O y c'] Fq :=
    { toFun := b₀
      map_add' := b₀.map_add
      map_smul' := fun r e => b₀.map_smulₛₗ r e }
  have hbc : IsBaseChange (𝔐.X.presheaf.stalk q.1) b' :=
    (GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange 𝔐.X 𝔐.t.G (CR O y c') P.x P.L P.M).2.2 (𝔐.X.presheaf.stalk q.1) Fq
      (LieVB.cast (R := 𝔐.X.presheaf.stalk q.1) h1.symm Mq) b' fun e =>
        (LieVB.cast_left (R := 𝔐.X.presheaf.stalk q.1) h1.symm Mq (b' e)).trans (hb₀ e)
  have hsp : ∀ z : Fq, jq z ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range P.toLi) := fun z =>
    hbc.inductionOn z (fun z => jq z ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range P.toLi)) (by simp)
      (fun m => Submodule.subset_span ⟨m, (hcomp m).symm⟩)
      (fun (s : 𝔐.X.presheaf.stalk q.1) n h => by
        have h5 : jq (s • n) = genMap 𝔐.ξ q s • jq n := jq.map_smulₛₗ s n
        rw [h5]
        exact Submodule.smul_mem _ (⟨genMap 𝔐.ξ q s, s, rfl⟩ : regAt 𝔐.ξ q) h)
      (fun a b ha hb => by
        rw [map_add]
        exact add_mem ha hb)
  refine le_antisymm (fun e he => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨v, hv⟩ := (𝔐.M.mem_lat_iff q e).1 he
    obtain ⟨z, rfl⟩ := Mq.onto v hv.1
    have hy : e = jq z := pt_left_inj 𝔐.M (hv.2.trans (hjq z).symm)
    rw [hy]
    exact hsp z
  · rintro _ ⟨v, rfl⟩
    exact (𝔐.M.mem_lat_iff q _).2 ⟨Mq.pt (b₀ v), Mq.tan _, by
      change (𝔐.M.pt (P.toLi v)).left = _
      rw [← hcomp]
      exact hjq _⟩

end Chart

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunPart

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunPart

open GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunAlg GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

section Sec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

abbrev OnChart (𝔐 : HodgeCpt Y S y) (O : Type) [CommRing O] [Algebra O Ω] (c' : ∀ k, J k) (q : Cpt 𝔐.ξ) : Prop :=
  InChart 𝔐.ξ (mseg y) c' q ∧ ∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q

def Dominated (P : ChartPack G O c') : Prop :=
  ∀ z : Spec (CommRingCat.of (CR O y c')), OnChart 𝔐 O c' ⟨P.x z, 𝔐.all _⟩ ∧
    ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r

theorem mem_chart_of_forall (P : ChartPack G O c') (hpt : Dominated P) (a : Ω)
    (ha : ∀ q, OnChart 𝔐 O c' q → a ∈ regAt 𝔐.ξ q) : a ∈ CR O y c' := by
  let I : Ideal (CR O y c') :=
    { carrier := {r | (r : Ω) * a ∈ CR O y c'}
      add_mem' := fun {u v} hu hv => by
        have h := (CR O y c').add_mem hu hv
        simpa [add_mul] using h
      zero_mem' := by simp [(CR O y c').zero_mem]
      smul_mem' := fun s r hr => by
        have h := (CR O y c').mul_mem s.2 hr
        change (s : Ω) * (r : Ω) * a ∈ CR O y c'
        rw [_root_.mul_assoc]
        exact h }
  by_cases hI : I = ⊤
  · have h1 : (1 : CR O y c') ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using h1
  · obtain ⟨n, hn, hle⟩ := Ideal.exists_le_maximal I hI
    let z : Spec (CommRingCat.of (CR O y c')) := ⟨n, hn.isPrime⟩
    obtain ⟨h1, h2⟩ := hpt z
    obtain ⟨r, s, hs, hsr⟩ := h2 a (ha _ h1)
    exact absurd (hle (show s ∈ I from show (s : Ω) * a ∈ CR O y c' by rw [hsr]; exact r.2)) hs

theorem mem_range_toLi_iff [Smooth 𝔐.t.G.hom] (P : ChartPack G O c') (hpt : Dominated P)
    (hψ : ∀ q, OnChart 𝔐 O c' q → ∃ ψ : CR O y c' →+* 𝔐.X.presheaf.stalk q.1,
      spMap ψ ≫ P.x = 𝔐.X.fromSpecStalk q.1 ∧ (genMap 𝔐.ξ q).comp ψ = algebraMap (CR O y c') Ω) (e : 𝔐.Li) :
    (∃ v, P.toLi v = e) ↔ ∀ q, OnChart 𝔐 O c' q → e ∈ 𝔐.M.lat q := by
  constructor
  · rintro ⟨v, rfl⟩ q hq
    obtain ⟨ψ, h1, h2⟩ := hψ q hq
    rw [lat_eq_span P q ψ h1 h2]
    exact Submodule.subset_span ⟨v, rfl⟩
  · intro he
    haveI := P.fin
    haveI := P.proj
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (CR O y c') P.L
    obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
    have hv : ∀ v, v = ∑ i, h v i • f (Pi.single i 1) := by
      intro v
      have h1 : f (h v) = v := LinearMap.congr_fun hh v
      conv_lhs => rw [← h1, pi_eq_sum_univ' (h v)]
      simp only [map_sum, map_smul]
    let g : Fin n → (P.L →ₗ[CR O y c'] Ω) := fun i =>
      (Algebra.linearMap (CR O y c') Ω) ∘ₗ (LinearMap.proj i) ∘ₗ h
    let Fi : Fin n → (𝔐.Li →ₗ[Ω] Ω) := fun i => P.toLi_bc.lift (g i)
    have hFi : ∀ i v, Fi i (P.toLi v) = (h v i : Ω) := fun i v => P.toLi_bc.lift_eq (g i) v
    have hmem : ∀ i, Fi i e ∈ CR O y c' := by
      intro i
      refine mem_chart_of_forall P hpt _ fun q hq => ?_
      obtain ⟨ψ, h1, h2⟩ := hψ q hq
      have h3 := he q hq
      rw [lat_eq_span P q ψ h1 h2] at h3
      refine (?_ : ∀ x ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range P.toLi), Fi i x ∈ regAt 𝔐.ξ q) e h3
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        rw [hFi]
        exact Fam.chartRing_le_regAt O y c' q hq.1 hq.2 (h v i).2
      | zero => simp [(regAt 𝔐.ξ q).zero_mem]
      | add x x' _ _ hx hx' =>
        rw [map_add]
        exact (regAt 𝔐.ξ q).add_mem hx hx'
      | smul s x _ hx =>
        have : Fi i (s • x) = (s : Ω) * Fi i x := by
          change Fi i ((s : Ω) • x) = _
          rw [map_smul, smul_eq_mul]
        rw [this]
        exact (regAt 𝔐.ξ q).mul_mem s.2 hx
    have hsum : ∀ w : 𝔐.Li, w = ∑ i, Fi i w • P.toLi (f (Pi.single i 1)) := by
      intro w
      refine P.toLi_bc.inductionOn w (fun w => w = ∑ i, Fi i w • P.toLi (f (Pi.single i 1))) (by simp) ?_ ?_ ?_
      · intro m
        conv_lhs => rw [hv m]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hFi, map_smul]
        exact (algebraMap_smul Ω (h m i) _).symm
      · intro s n hn
        conv_lhs => rw [hn]
        simp only [map_smul, Finset.smul_sum, smul_eq_mul, mul_smul]
      · intro a b ha hb
        conv_lhs => rw [ha, hb]
        simp only [map_add, add_smul, Finset.sum_add_distrib]
    refine ⟨∑ i, (⟨Fi i e, hmem i⟩ : CR O y c') • f (Pi.single i 1), ?_⟩
    conv_rhs => rw [hsum e]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    exact algebraMap_smul Ω (⟨Fi i e, hmem i⟩ : CR O y c') _

end Sec

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunPart

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunPart

open GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunAlg GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

theorem mem_coordLat_dR_iff (P : ChartPack G O c')
    (hsec : ∀ e, (∃ v, P.toLi v = e) ↔ ∀ q, OnChart 𝔐 O c' q → e ∈ 𝔐.M.lat q)
    (s : CMType H ⊕ CMType H) {r : ℕ} (b : Fin r → 𝔐.Li) (hb : ∀ k, b k ∈ 𝔐.Vgen s) (a : Fin r → Ω) :
    a ∈ coordLat O y (𝔐.dR s) b c' ↔ ∃ v, P.toLi v = ∑ k, a k • b k := by
  rw [Fam.mem_coordLat_iff, hsec]
  have hV : ∑ k, a k • b k ∈ 𝔐.Vgen s := sum_mem fun k _ => Submodule.smul_mem _ _ (hb k)
  constructor
  · intro h q hq
    exact (Submodule.mem_inf.1 (h q hq.1 hq.2)).1
  · intro h q h1 h2
    exact Submodule.mem_inf.2 ⟨h q ⟨h1, h2⟩, hV⟩

theorem ev_mem_dotDual (P : ChartPack G O c')
    (hsec : ∀ e, (∃ v, P.toLi v = e) ↔ ∀ q, OnChart 𝔐 O c' q → e ∈ 𝔐.M.lat q)
    (s : CMType H ⊕ CMType H) {r : ℕ} (b : Fin r → 𝔐.Li) (hb : ∀ k, b k ∈ 𝔐.Vgen s)
    (u : Module.Dual (CR O y c') P.L) :
    (fun k => P.j u (b k)) ∈ dotDual (CR O y c') (coordLat O y (𝔐.dR s) b c') := by
  rw [mem_dotDual_iff]
  intro l hl
  obtain ⟨v, hv⟩ := (mem_coordLat_dR_iff P hsec s b hb l).1 hl
  have h1 : l ⬝ᵥ (fun k => P.j u (b k)) = P.j u (∑ k, l k • b k) := by
    simp [dotProduct, map_sum, smul_eq_mul]
  rw [h1, ← hv, P.j_apply]
  exact (u v).2

theorem exists_form [CharZero Ω] (P : ChartPack G O c')
    (hsec : ∀ e, (∃ v, P.toLi v = e) ↔ ∀ q, OnChart 𝔐 O c' q → e ∈ 𝔐.M.lat q)
    (s : CMType H ⊕ CMType H) {r : ℕ} (b : Fin r → 𝔐.Li) (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = 𝔐.Vgen s) (hemb : ∀ a, 𝔐.emb s a ∈ CR O y c')
    (hd : (((discr E : ℤ) : Ω))⁻¹ ∈ CR O y c') (hd0 : ((discr E : ℤ) : Ω) ≠ 0) (m : Fin r → Ω)
    (hm : m ∈ dotDual (CR O y c') (coordLat O y (𝔐.dR s) b c')) :
    ∃ u : Module.Dual (CR O y c') P.L, (∀ k, P.j u (b k) = m k) ∧
      ∀ (a : 𝓞 E) v, ((u (P.ρ a v) : CR O y c') : Ω) = 𝔐.emb s a * ((u v : CR O y c') : Ω) := by
  classical
  have hb : ∀ k, b k ∈ 𝔐.Vgen s := fun k => hsp ▸ Submodule.subset_span ⟨k, rfl⟩
  let τ : E →+* Ω := IsFractionRing.lift (EigSplit.injective_of_charZero E (𝔐.emb s))
  have hτ : ∀ a : 𝓞 E, τ (a : E) = 𝔐.emb s a := fun a =>
    IsFractionRing.lift_algebraMap (EigSplit.injective_of_charZero E (𝔐.emb s)) a
  have heig : 𝔐.Vgen s = HT.eigSp 𝔐.ρ τ := by
    ext v
    simp [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, HT.eigSp, Submodule.mem_iInf, sub_eq_zero, hτ]
  obtain ⟨s1, s2, -, s4⟩ := HT.ProjEig.eigProj_spec Ω 𝔐.Li E 𝔐.ρ τ
  have hcoef : ∀ k, τ (HT.dualInt E k) ∈ CR O y c' := by
    intro k
    obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E _ (EigSplit.discr_mem_differentIdeal E) k
    have h1 : 𝔐.emb s z = ((discr E : ℤ) : Ω) * τ (HT.dualInt E k) := by
      rw [← hτ, hz, map_mul]
      simp
    have h2 : τ (HT.dualInt E k) = ((discr E : ℤ) : Ω)⁻¹ * 𝔐.emb s z := by
      rw [h1, inv_mul_cancel_left₀ hd0]
    rw [h2]
    exact (CR O y c').mul_mem hd (hemb z)
  have hproj : ∀ x : P.L, ∃ x', P.toLi x' = HT.eigProj 𝔐.ρ τ (P.toLi x) := by
    intro x
    refine ⟨∑ k, (⟨_, hcoef k⟩ : CR O y c') • P.ρ (RingOfIntegers.basis E k) x, ?_⟩
    rw [map_sum]
    simp only [HT.eigProj, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, toLi_rho]
    exact (algebraMap_smul Ω (⟨_, hcoef k⟩ : CR O y c') _).symm
  let B := Module.Basis.span hli
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (B.constr Ω m)
  have hψb : ∀ k, ψ (b k) = m k := by
    intro k
    have h1 := LinearMap.congr_fun hψ (B k)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.constr_basis] at h1
    rwa [Module.Basis.span_apply] at h1
  let Ψ : 𝔐.Li →ₗ[Ω] Ω := ψ ∘ₗ HT.eigProj 𝔐.ρ τ
  have hΨ : ∀ x : P.L, Ψ (P.toLi x) ∈ CR O y c' := by
    intro x
    obtain ⟨x', hx'⟩ := hproj x
    have h1 : HT.eigProj 𝔐.ρ τ (P.toLi x) ∈ Submodule.span Ω (Set.range b) := by
      rw [hsp, heig]
      exact s1 _
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 h1
    have h2 : a ∈ coordLat O y (𝔐.dR s) b c' :=
      (mem_coordLat_dR_iff P hsec s b hb a).2 ⟨x', hx'.trans ha.symm⟩
    have h3 := (mem_dotDual_iff _ _ _).1 hm a h2
    have h4 : Ψ (P.toLi x) = a ⬝ᵥ m := by
      change ψ (HT.eigProj 𝔐.ρ τ (P.toLi x)) = _
      rw [← ha, map_sum]
      simp [dotProduct, hψb]
    rw [h4]
    exact h3
  let u : Module.Dual (CR O y c') P.L :=
    { toFun := fun x => ⟨_, hΨ x⟩
      map_add' := fun x x' => Subtype.ext (by simp)
      map_smul' := fun t x => Subtype.ext (by
        change Ψ (P.toLi (t • x)) = (t : Ω) * Ψ (P.toLi x)
        rw [map_smul, ← algebraMap_smul Ω t (P.toLi x), map_smul]
        rfl) }
  have hju : ∀ w, P.j u w = Ψ w := by
    intro w
    refine P.toLi_bc.inductionOn w (fun w => P.j u w = Ψ w) (by simp) (fun v => ?_) (fun t n hn => ?_)
      (fun a a' ha ha' => ?_)
    · rw [P.j_apply]
      rfl
    · rw [map_smul, map_smul, hn]
    · rw [map_add, map_add, ha, ha']
  refine ⟨u, fun k => ?_, fun a v => ?_⟩
  · rw [hju]
    change ψ (HT.eigProj 𝔐.ρ τ (b k)) = _
    rw [s2 _ (heig ▸ hb k), hψb]
  · change Ψ (P.toLi (P.ρ a v)) = 𝔐.emb s a * Ψ (P.toLi v)
    rw [toLi_rho]
    change ψ (HT.eigProj 𝔐.ρ τ (𝔐.ρ a (P.toLi v))) = _
    have h1 : HT.eigProj 𝔐.ρ τ (𝔐.ρ a (P.toLi v)) = 𝔐.ρ a (HT.eigProj 𝔐.ρ τ (P.toLi v)) :=
      LinearMap.congr_fun (s4 a) _
    have h2 : 𝔐.ρ a (HT.eigProj 𝔐.ρ τ (P.toLi v)) = 𝔐.emb s a • HT.eigProj 𝔐.ρ τ (P.toLi v) := by
      have h3 : HT.eigProj 𝔐.ρ τ (P.toLi v) ∈ 𝔐.Vgen s := heig ▸ s1 _
      have h4 := (Submodule.mem_iInf _).1 h3 a
      simpa [sub_eq_zero] using h4
    rw [h1, h2, map_smul, smul_eq_mul]
    rfl

end Form

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunPart

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

open GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunAlg GlobalTheory.CompanionTheory.Ar.Num.FamEx.FunPart

theorem chartD_fun_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), LocFree (CR O y c') (Fintype.card F ^ (D.p + D.q)) (chartD e b pq sc w P i).M ∧ (chartD e b pq sc w P i).M ≤ stdLat (CR O y c') _ ∧ (∃ m : ℕ, mulLat ((p : Ω) ^ m) (stdLat (CR O y c') _) ≤ (chartD e b pq sc w P i).M) ∧ (1 : (Fin (D.p + D.q) → F) → Ω) ∈ (chartD e b pq sc w P i).M ∧ ∀ τ, (∀ a ∈ CR O y c', ∀ v ∈ (chartD e b pq sc w P i).Th τ, a • v ∈ (chartD e b pq sc w P i).Th τ) ∧ (∀ g, (∃ m, (g, m) ∈ (chartD e b pq sc w P i).Th τ) ↔ g ∈ (chartD e b pq sc w P i).M ∧ g 0 = 0) ∧ (∀ m, (∃ g, (g, m) ∈ (chartD e b pq sc w P i).Th τ) ↔ m ∈ dotDual (CR O y c') ((chartD e b pq sc w P i).lie τ)) ∧ ∀ m, (0, m) ∈ (chartD e b pq sc w P i).Th τ ↔ m ∈ mulLat (p : Ω) (dotDual (CR O y c') ((chartD e b pq sc w P i).lie τ)) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d harith hpq p _ hpS hHT hp2 hdisc b hb φ hφ A _ _ _ m _ hpm
    O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ hO hsc G c' hc P i
  classical
  obtain ⟨-, -, -, -, hres, -, ⟨-, -, hpnu⟩, -⟩ := hO
  have hpp : p.Prime := Fact.out
  obtain ⟨hnoeth, hint, -⟩ := GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartRing_noetherian_normal_fraction E H D l Xo c O₀ β Y S Ω K J y 𝔐 d harith p hpS A m hpm O c' hc
  haveI := hnoeth
  haveI := hint
  haveI hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  haveI : Finite (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    simpa [Ideal.span_singleton_eq_bot] using hpp.ne_zero)
  haveI : Finite (TorsT E (D.p + D.q) p) := inferInstanceAs (Finite (Multiplicative _))
  obtain ⟨hHopf, -, -, hend, -, hθ⟩ := GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ 𝔐.X 𝔐.t.G P.x p P.i₁
    P.tors₁ hsm
  obtain ⟨θ, ⟨hsurj, hder⟩, hker, -⟩ := hθ P.L P.M
  obtain ⟨ε, hε1, hε⟩ := exists_eps hsc
  haveI : IsMonHom (𝔐.t.act.act ε) := 𝔐.t.act.hom ε
  have hst : ∀ f ∈ P.Γ₁.btOrder ⊤, (fun t => f (toN sc (fromN pq t))) ∈ P.Γ₁.btOrder ⊤ := fun f hf =>
    hend (𝔐.t.act.act ε) (idem pq sc) (pts_idem P hε) f hf
  have hn : ∀ x : omega (P.Γ₁.btOrder ⊤), (p : CR O y c') • x = 0 := by
    intro x
    obtain ⟨u, rfl⟩ := hsurj x
    rw [← LinearMap.map_smul]
    exact (hker _).2 ⟨u, Nat.cast_smul_eq_nsmul _ _ _⟩
  obtain ⟨k, hk⟩ := exists_pow_smul_mem hHopf (p : CR O y c') hn
  have hM : ∀ g, g ∈ funLat P sc ↔ ∃ f ∈ P.Γ₁.btOrder ⊤, ∀ a, ((f (toN sc a) : CR O y c') : Ω) = g a := by
    intro g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, hf, fun a => rfl⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨f, hf, funext h⟩
  have hMR : ∀ a ∈ CR O y c', ∀ g ∈ funLat P sc, a • g ∈ funLat P sc := by
    intro a ha g hg
    obtain ⟨f, hf, h⟩ := (hM g).1 hg
    refine (hM _).2 ⟨(⟨a, ha⟩ : CR O y c') • f, Subalgebra.smul_mem _ hf _, fun x => ?_⟩
    change a * ((f (toN sc x) : CR O y c') : Ω) = a * g x
    rw [h]
  have hck : (((p : CR O y c') ^ k : CR O y c') : Ω) = (p : Ω) ^ k := by simp
  obtain ⟨l1, l2, l3, l4⟩ := lat_clauses (CR O y c') hHopf (toN sc) (fromN pq) (fromN_toN hsc) hst
    ((p : CR O y c') ^ k) (by rw [hck]; exact pow_ne_zero _ hpΩ) hk (funLat P sc) hM
  have hP : Dominated P := fun z => by
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartPoint_inChart_dominated E H D l Xo c O₀ β Y S Ω K J y 𝔐 d harith p hpS A m hpm O G c' hc P z
    exact ⟨⟨h1, h2⟩, h3⟩
  have hψ : ∀ q, OnChart 𝔐 O c' q → ∃ ψ : CR O y c' →+* 𝔐.X.presheaf.stalk q.1,
      spMap ψ ≫ P.x = 𝔐.X.fromSpecStalk q.1 ∧ (genMap 𝔐.ξ q).comp ψ = algebraMap (CR O y c') Ω := by
    intro q hq
    obtain ⟨U, hU, hUq⟩ := 𝔐.tie.affine c' hc
    let ψ₀ : CR O y c' →+* regAt 𝔐.ξ q := (algebraMap (CR O y c') Ω).codRestrict (regAt 𝔐.ξ q)
      fun a => Fam.chartRing_le_regAt O y c' q hq.1 hq.2 a.2
    let ψ : CR O y c' →+* 𝔐.X.presheaf.stalk q.1 :=
      ((LieStalk.regIso 𝔐.tie.gen q).symm : regAt 𝔐.ξ q →+* 𝔐.X.presheaf.stalk q.1).comp ψ₀
    have h2 : (genMap 𝔐.ξ q).comp ψ = algebraMap (CR O y c') Ω := by
      ext a
      exact LieStalk.genMap_regIso_symm 𝔐.tie.gen q (ψ₀ a)
    exact ⟨ψ, GlobalTheory.CompanionTheory.Ar.Num.FamEx.StalkPt.spMap_eq_fromSpecStalk 𝔐.X Ω 𝔐.ξ 𝔐.tie.gen U hU (CR O y c') (algebraMap (CR O y c') Ω) P.x P.x_gen
      (fun z => (hUq _).2 ⟨𝔐.all _, (hP z).1.1⟩) q ((hUq _).2 ⟨q.2, hq.1⟩) ψ h2, h2⟩
  have hsec := mem_range_toLi_iff P hP hψ

  obtain ⟨dv, hdv⟩ : ∃ u : O, u * ((discr E : ℤ) : O) = 1 := by
    have hcop : IsCoprime (p : ℤ) (discr E) :=
      (Nat.prime_iff_prime_int.1 hpp).irreducible.coprime_iff_not_dvd.2 hdisc
    obtain ⟨a', b', hab⟩ := hcop
    have h1 : (a' : O) * (p : O) + (b' : O) * ((discr E : ℤ) : O) = 1 := by exact_mod_cast congrArg (Int.cast (R := O)) hab
    by_contra hne
    have hnu : ¬ IsUnit (((discr E : ℤ) : O)) := fun hu => hne (by
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      exact ⟨v, hv⟩)
    have hm1 : (a' : O) * (p : O) ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hpnu)
    have hm2 : (b' : O) * ((discr E : ℤ) : O) ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    have := Ideal.add_mem _ hm1 hm2
    rw [h1] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this isUnit_one
  have hdΩ : algebraMap O Ω dv * ((discr E : ℤ) : Ω) = 1 := by
    have := congrArg (algebraMap O Ω) hdv
    simpa using this
  have hd0 : ((discr E : ℤ) : Ω) ≠ 0 := right_ne_zero_of_mul_eq_one hdΩ
  have hdinv : (((discr E : ℤ) : Ω))⁻¹ ∈ CR O y c' := by
    rw [← eq_inv_of_mul_eq_one_left hdΩ]
    exact Subalgebra.algebraMap_mem _ dv
  refine ⟨?_, l2, ⟨k, ?_⟩, l4, fun τ => ?_⟩
  · have hcard : Fintype.card (Fin (D.p + D.q) → F) = Fintype.card F ^ (D.p + D.q) := by simp
    rw [← hcard]
    exact l1
  · rintro _ ⟨h, hh, rfl⟩
    have := l3 h hh
    rw [hck] at this
    exact this
  · have hbτ : ∀ k, b (e τ) k ∈ 𝔐.Vgen (e τ) := fun k => (hb (e τ)).2 ▸ Submodule.subset_span ⟨k, rfl⟩
    have hemb : ∀ a, 𝔐.emb (e τ) a ∈ CR O y c' := fun a => by
      obtain ⟨o, ho, -⟩ := hres τ a
      rw [← ho]
      exact Subalgebra.algebraMap_mem _ o
    let ev : Module.Dual (CR O y c') P.L →ₗ[CR O y c'] (Fin (labelRk D (e τ)) → Ω) :=
      { toFun := fun u k => P.j u (b (e τ) k)
        map_add' := fun u u' => funext fun k => by simp
        map_smul' := fun t u => funext fun k => by simp }
    have H1 : ∀ u, ev u ∈ dotDual (CR O y c') (coordLat O y (𝔐.dR (e τ)) (b (e τ)) c') := fun u =>
      ev_mem_dotDual P hsec (e τ) (b (e τ)) hbτ u

    obtain ⟨κ, hκ⟩ : ∃ κ : CR O y c', 𝔐.emb (e τ) ε = 1 + (p : Ω) * (κ : Ω) := by
      obtain ⟨o, ho, hor⟩ := hres τ ε
      have hunit : IsUnit o := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hor, hε1, map_one]
        exact one_ne_zero
      obtain ⟨v₀, hv₀⟩ := hunit.exists_left_inv
      have hidem : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) (ε * ε - ε) = 0 := by
        have h1 := hε (Ideal.Quotient.mk _ ε)
        rw [hε1] at h1
        have h2 := hε 1
        rw [map_one, _root_.mul_one] at h2
        rw [map_sub, map_mul, h1, h2, sub_self]
      obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hidem)
      have h3 : 𝔐.emb (e τ) ε * 𝔐.emb (e τ) ε - 𝔐.emb (e τ) ε = (p : Ω) * 𝔐.emb (e τ) c₀ := by
        have := congrArg (𝔐.emb (e τ)) hc₀
        simpa using this
      have h4 : algebraMap O Ω v₀ * 𝔐.emb (e τ) ε = 1 := by
        rw [← ho, ← map_mul, hv₀, map_one]
      refine ⟨⟨algebraMap O Ω v₀ * 𝔐.emb (e τ) c₀,
        (CR O y c').mul_mem (Subalgebra.algebraMap_mem _ v₀) (hemb c₀)⟩, ?_⟩
      change 𝔐.emb (e τ) ε = 1 + (p : Ω) * (algebraMap O Ω v₀ * 𝔐.emb (e τ) c₀)
      linear_combination (algebraMap O Ω v₀) * h3 + (1 - 𝔐.emb (e τ) ε) * h4
    have H2 : ∀ m ∈ dotDual (CR O y c') (coordLat O y (𝔐.dR (e τ)) (b (e τ)) c'), ∃ u, ev u = m ∧
        ∃ f : augSub (P.Γ₁.btOrder ⊤), (∀ t, f.1 (toN sc (fromN pq t)) = f.1 t) ∧
          θ u = augCl (P.Γ₁.btOrder ⊤) f := by
      intro m' hm'
      obtain ⟨u, hu1, hu2⟩ := exists_form P hsec (e τ) (b (e τ)) (hb (e τ)).1 (hb (e τ)).2 hemb hdinv hd0 m' hm'
      have hw : u ∘ₗ P.ρ ε = u + p • (κ • u) := by
        ext v
        change ((u (P.ρ ε v) : CR O y c') : Ω) = ((u v + p • (κ * u v) : CR O y c') : Ω)
        rw [hu2, hκ]
        simp
        ring
      obtain ⟨f₀, hf₀⟩ := augCl_surjective (P.Γ₁.btOrder ⊤) (θ u)
      have d₀ := (hder (toAug f₀) u).1 hf₀.symm
      have d₁ := GlobalTheory.CompanionTheory.Ar.Num.FamEx.isDerAtOne_comp_endo (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ 𝔐.X 𝔐.t.G P.x P.i₁ p P.tors₁ P.L P.M
        (𝔐.t.act.act ε) (P.ρ ε) (P.act ε) (idem pq sc) (pts_idem P hε) _ u d₀
      let f₁ : augSub (P.Γ₁.btOrder ⊤) := ⟨fun t => f₀.1 (idem pq sc t), hst _ f₀.2.1, by
        change f₀.1 (idem pq sc 1) = 0
        rw [map_one]
        exact f₀.2.2⟩
      have h3 : θ (u ∘ₗ P.ρ ε) = augCl (P.Γ₁.btOrder ⊤) f₁ := (hder (toAug f₁) _).2 d₁
      have h4 : θ (u ∘ₗ P.ρ ε) = θ u := by
        rw [hw, map_add, (hker _).2 ⟨_, rfl⟩, add_zero]
      refine ⟨u, funext hu1, f₁, fun t => ?_, h4.symm.trans h3⟩
      change f₀.1 (idem pq sc (idem pq sc t)) = f₀.1 (idem pq sc t)
      have hi : idem pq sc (idem pq sc t) = idem pq sc t := by
        change toN sc (fromN pq (toN sc (fromN pq t))) = toN sc (fromN pq t)
        rw [fromN_toN hsc]
      rw [hi]
    exact th_clauses (CR O y c') (toN sc) (fromN pq) (fromN_one pq) (toN_zero sc) (fromN_toN hsc) hst (funLat P sc) hM
      hMR (augSub (P.Γ₁.btOrder ⊤)) (fun f => Iff.rfl) (augCl (P.Γ₁.btOrder ⊤)) θ hsurj
      (fun f u => P.Γ₁.IsDerAtOne P.i₁ P.M p f u) (fun f w => hder (toAug f) w) p hker ev _ H1 H2 _ rfl

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
