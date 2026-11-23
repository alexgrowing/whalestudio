import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantEqOfIndependentGenericTuplesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAlgClosedTransversalStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversallyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantFromIntersectionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaIndep

theorem exists_coords {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) :
    ∃ s : RR x l, Coords x b c s.f := by
  refine ⟨⟨fun i => ∑ k, cst x.P.A.hom ((pw x.P.L (l : ℤ)).U i) (c k) * (b k).f i, ?_⟩, fun i => rfl⟩
  intro i j
  have e4 : ∀ (V W : x.P.A.left.Opens) (h : W ≤ V) (a : R),
      (x.P.A.left.presheaf.map (homOfLE h).op).hom (cst x.P.A.hom V a) = cst x.P.A.hom W a := by
    intro V W h a
    simp only [AbLaw.cst, RingHom.comp_apply]
    exact GlobalTheory.KeyVia.res_appLE (φ := x.P.A.hom) (U := ⊤) _ h _
  simp only [map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e3 := (b k).compat i j
  rw [e4, e4, e3]
  ring

theorem eq_of_coords {R : Type} [CommRing R] {x : KeyIn R} {l N : ℕ} {b : Fin N → RR x l} {c : Fin N → R}
    {s t : RR x l} (hs : Coords x b c s.f) (ht : Coords x b c t.f) : s = t := by
  have hf : s.f = t.f := funext fun i => (hs i).trans (ht i).symm
  cases s
  cases t
  cases hf
  rfl

theorem degProd_ne_zero {g n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (h : admitted g n l l' al) :
    degProd g n l l' ≠ 0 := by
  obtain ⟨-, hl, hl', -⟩ := h
  unfold degProd
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjn : j * n ≤ g * n := Nat.mul_le_mul_right n hj'
  apply mul_ne_zero <;> omega

variable {K : Type} [Field K] {x : KeyIn K} {n : ℕ}

def Framed (b : Fin (n ^ x.P.g) → RR x n) {R : Type} [CommRing R] (f : K →+* R)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (x' : KeyIn R) (s : Fin x'.P.g → RR x' n) : Prop :=
  ∃ φ w, ∃ (hg : x'.P.g = x.P.g) (b' : Fin (n ^ x.P.g) → RR x' n), KeyVia x' x f φ w ∧
    (∀ k, SecVia x' x φ w (b' k) (b k)) ∧ ∀ i, Coords x' b' (fun k => T (i.cast hg, k)) (s i).f

variable {b : Fin (n ^ x.P.g) → RR x n}

theorem exists_framed (b : Fin (n ^ x.P.g) → RR x n) {R : Type} [CommRing R] (f : K →+* R)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) : ∃ x' s, Framed b f T x' s := by
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, H⟩ := (GlobalTheory.KeyVia.main K R x x' f).1.1 hx'
  obtain ⟨_, hg, _⟩ := id H
  have M := (GlobalTheory.KeyVia.main K R x x' f).2 φ w H
  choose b' hb' _ using fun k => M.1 n (b k)
  choose s hs using fun i : Fin x'.P.g => exists_coords x' b' (fun k => T (i.cast hg, k))
  exact ⟨x', s, φ, w, hg, b', H, hb', hs⟩

theorem Framed.g_eq {R : Type} [CommRing R] {f : K →+* R} {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R}
    {s : Fin x'.P.g → RR x' n} (h : Framed b f T x' s) : x'.P.g = x.P.g := by
  obtain ⟨_, _, hg, _⟩ := h
  exact hg

theorem Framed.via {R R' : Type} [CommRing R] [CommRing R'] {f : K →+* R} {j : R →+* R'}
    {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R} {s : Fin x'.P.g → RR x' n} {x'' : KeyIn R'}
    {s' : Fin x''.P.g → RR x'' n} (h : Framed b f T x' s) (h' : Framed b (j.comp f) (j ∘ T) x'' s') :
    ∃ φ w, ∃ hg : x''.P.g = x'.P.g, KeyVia x'' x' j φ w ∧ ∀ i, SecVia x'' x' φ w (s' i) (s (i.cast hg)) := by
  obtain ⟨φ1, w1, hg1, b1, H1, hb1, hs1⟩ := h
  obtain ⟨φ2, w2, hg2, b2, H2, hb2, hs2⟩ := h'
  obtain ⟨φ, w, H, -, hsec⟩ := GlobalTheory.KaLift.keyVia_cancel H1 H2
  have hg : x''.P.g = x'.P.g := hg2.trans hg1.symm
  refine ⟨φ, w, hg, H, fun i => ?_⟩
  have hb : ∀ k, SecVia x'' x' φ w (b2 k) (b1 k) := fun k => hsec n (b k) (b1 k) (b2 k) (hb1 k) (hb2 k)
  have M := (GlobalTheory.KeyVia.main R R' x' x'' j).2 φ w H
  obtain ⟨t, ht, -⟩ := M.1 n (s (i.cast hg))
  have hc := M.2.2 n (n ^ x.P.g) b1 b2 (s (i.cast hg)) t (fun k => T ((i.cast hg).cast hg1, k)) hb ht (hs1 _)
  have e : (i.cast hg).cast hg1 = i.cast hg2 := Fin.ext rfl
  rw [e] at hc
  have ht' : t = s' i := eq_of_coords hc (hs2 i)
  rw [← ht']
  exact ht

variable {l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}

theorem Framed.kaVal (hL : Out.Laws) (hA : admitted x.P.g n l l' al) {R R' : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] {f : K →+* R} {j : R →+* R'}
    {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R} {s : Fin x'.P.g → RR x' n} {x'' : KeyIn R'}
    {s' : Fin x''.P.g → RR x'' n} (h : Framed b f T x' s) (h' : Framed b (j.comp f) (j ∘ T) x'' s') {κ : Rˣ}
    (hκ : KaVal x' n l l' al s κ) : KaVal x'' n l l' al s' (Units.map j.toMonoidHom κ) := by
  obtain ⟨φ, w, hg, H, hs⟩ := h.via h'
  have hA' : admitted x'.P.g n l l' al := by rw [h.g_eq]; exact hA
  exact GlobalTheory.T.keyInvariant_baseChange hL R R' x' x'' j φ w n l l' al hg s s' κ hA' H hs hκ

def ValAt (b : Fin (n ^ x.P.g) → RR x n) (l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (R : Type) [CommRing R]
    [Algebra K R] (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) : Prop :=
  ∃ x' s, ∃ κ : Rˣ, Framed b (algebraMap K R) T x' s ∧ KaVal x' n l l' al s κ ∧ a = κ

theorem valAt_map (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (R R' : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R')
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) (h : ValAt b l l' al R T a) : ValAt b l l' al R' (j ∘ T) (j a) := by
  obtain ⟨x', s, κ, hf, hκ, rfl⟩ := h
  obtain ⟨x'', s'', hf''⟩ := exists_framed b (algebraMap K R') (j ∘ T)
  have e : (j : R →+* R').comp (algebraMap K R) = algebraMap K R' := j.comp_algebraMap
  have hf2 : Framed b ((j : R →+* R').comp (algebraMap K R)) ((j : R →+* R') ∘ T) x'' s'' := by
    rw [e]; exact hf''
  exact ⟨x'', s'', _, hf'', hf.kaVal hL hA hf2 hκ, rfl⟩

theorem valAt_unique [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (F : Type) [Field F] [Algebra K F]
    (T : Fin x.P.g × Fin (n ^ x.P.g) → F) (a a' : F) (h : ValAt b l l' al F T a) (h' : ValAt b l l' al F T a') :
    a = a' := by
  obtain ⟨x1, s1, κ1, h1, hk1, rfl⟩ := h
  obtain ⟨x2, s2, κ2, h2, hk2, rfl⟩ := h'
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have h2' : Framed b ((RingHom.id F).comp (algebraMap K F)) (RingHom.id F ∘ T) x2 s2 := by
    simpa only [RingHom.id_comp, RingHom.coe_id, Function.id_comp] using h2
  have hk := h1.kaVal hL hA h2' hk1
  have hA2 : admitted x2.P.g n l l' al := by rw [h2.g_eq]; exact hA
  have e := GlobalTheory.T.keyInvariantFromIntersection_unique hL F x2 n l l' al s2 _ _ hA2 hk hk2
  rw [← e]
  rfl

theorem exists_valAt [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (hb : IsBasis x b) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (T : Fin x.P.g × Fin (n ^ x.P.g) → Ω) (hT : AlgebraicIndependent K T) :
    ∃ a, ValAt b l l' al Ω T a := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨x', s, hf⟩ := exists_framed b (algebraMap K Ω) T
  obtain ⟨φ, w, hg, b', H, hb', hs⟩ := id hf
  have hA' : admitted x'.P.g n l l' al := by rw [hg]; exact hA
  have hinj : Function.Injective
      (fun p : Fin x'.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g))) :=
    fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)
  obtain ⟨d, z, ch, hz⟩ := GlobalTheory.T.generic_sections_meet_transversally hL K Ω x x' φ w n b b' (fun p => T (p.1.cast hg, p.2)) s hA.1 H hb hb'
    (hT.comp _ hinj) hs
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_keyInvariant_algClosed_transversal hL Ω x' n l l' al d s z ch hA'
    (Nat.cast_ne_zero.mpr (degProd_ne_zero hA')) hz
  exact ⟨κ, x', s, κ, hf, hκ, rfl⟩

theorem valAt_generic [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (hb : IsBasis x b) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (T T' : Fin x.P.g × Fin (n ^ x.P.g) → Ω) (a a' : Ω)
    (hT : AlgebraicIndependent K (Sum.elim T T')) (h : ValAt b l l' al Ω T a) (h' : ValAt b l l' al Ω T' a') :
    a = a' := by
  obtain ⟨x1, s1, κ1, h1, hk1, rfl⟩ := h
  obtain ⟨x2, s2, κ2, h2, hk2, rfl⟩ := h'
  obtain ⟨φ, w, hg, b', H, hb', hs1⟩ := id h1
  choose s3 hs3 using fun i : Fin x1.P.g => exists_coords x1 b' (fun k => T' (i.cast hg, k))
  have h3 : Framed b (algebraMap K Ω) T' x1 s3 := ⟨φ, w, hg, b', H, hb', hs3⟩
  have h3' : Framed b ((RingHom.id Ω).comp (algebraMap K Ω)) (RingHom.id Ω ∘ T') x1 s3 := by
    simpa only [RingHom.id_comp, RingHom.coe_id, Function.id_comp] using h3
  have hk3 := h2.kaVal hL hA h3' hk2
  have hinj : Function.Injective
      (fun p : Fin x1.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g))) :=
    fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)
  have hind := hT.comp _ (Sum.map_injective.mpr ⟨hinj, hinj⟩)
  rw [Sum.elim_comp_map] at hind
  have e := GlobalTheory.T.keyInvariant_eq_of_independent_generic_tuples hL K Ω x x1 φ w n l l' al b b' (fun p => T (p.1.cast hg, p.2))
    (fun p => T' (p.1.cast hg, p.2)) s1 s3 κ1 _ hA H hb hb' hind hs1 hs3 hk1 hk3
  rw [e]
  rfl

theorem valAt_lift [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → O) (a : Ω) (hr : RingHom.ker r = IsLocalRing.maximalIdeal O)
    (h : ValAt b l l' al Ω (r ∘ T) a) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
      (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧
        ValAt b l l' al O' (j ∘ T) u := by
  obtain ⟨xΩ, sΩ, κ, hΩ, hκ, rfl⟩ := h
  obtain ⟨xO, sO, hO⟩ := exists_framed b (algebraMap K O) T
  have hΩ' : Framed b ((r : O →+* Ω).comp (algebraMap K O)) ((r : O →+* Ω) ∘ T) xΩ sΩ := by
    rw [r.comp_algebraMap]; exact hΩ
  obtain ⟨φ, w, hg, H, hs⟩ := hO.via hΩ'
  obtain ⟨z, ch, _, _, _, _, _, _, _, hz, _⟩ := id hκ
  have hAO : admitted xO.P.g n l l' al := by rw [hO.g_eq]; exact hA
  have hu : IsUnit ((degProd xO.P.g n l l' : ℕ) : O) := by
    have h0 : ((degProd xO.P.g n l l' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (degProd_ne_zero hAO)
    have := (IsUnit.mk0 _ h0).map (algebraMap K O)
    rwa [map_natCast] at this
  obtain ⟨O', i1, i2, i3, j, r', x', φ', w', hg', s', u, hj, -, hr', H', hs', hu'⟩ :=
    GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O Ω (r : O →+* Ω) xO xΩ φ w n l l' al _ hg sO sΩ z ch hr hAO hu H hs hz
  letI : Algebra K O' := (j.comp (algebraMap K O)).toAlgebra
  let jA : O →ₐ[K] O' := { toRingHom := j, commutes' := fun c => rfl }
  let rA : O' →ₐ[K] Ω :=
    { toRingHom := r', commutes' := fun c => by
        show r' (j (algebraMap K O c)) = algebraMap K Ω c
        rw [← RingHom.comp_apply, hr']
        exact r.commutes c }
  refine ⟨O', i1, i2, i3, inferInstance, jA, rA, (u : O'), hj, ?_, ?_⟩
  · ext c
    show r' (j c) = r c
    rw [← RingHom.comp_apply, hr']
    rfl
  · obtain ⟨x'', s'', h''⟩ := exists_framed b (algebraMap K O') (jA ∘ T)
    have h2 : Framed b (j.comp (algebraMap K O)) (j ∘ T) x'' s'' := h''
    obtain ⟨φ2, w2, hg2, H2, hs2⟩ := hO.via h2
    have H2' : KeyVia x'' xO ((RingHom.id O').comp j) φ2 w2 := by rw [RingHom.id_comp]; exact H2
    obtain ⟨φ3, w3, H3, -, hsec⟩ := GlobalTheory.KaLift.keyVia_cancel H' H2'
    have hg3 : x''.P.g = x'.P.g := hg2.trans hg'.symm
    have hs3 : ∀ i, SecVia x'' x' φ3 w3 (s'' i) (s' (i.cast hg3)) := by
      intro i
      have h1 := hs' (i.cast hg3)
      have e : (i.cast hg3).cast hg' = i.cast hg2 := Fin.ext rfl
      rw [e] at h1
      exact hsec n (sO (i.cast hg2)) (s' (i.cast hg3)) (s'' i) h1 (hs2 i)
    have hA' : admitted x'.P.g n l l' al := by rw [hg']; exact hAO
    have hk := GlobalTheory.T.keyInvariant_baseChange hL O' O' x' x'' (RingHom.id O') φ3 w3 n l l' al hg3 s' s'' u hA' H3 hs3 hu'
    exact ⟨x'', s'', _, h'', hk, rfl⟩

theorem kaVal_independent : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted x.P.g n l l' al → ∃ κ : Kˣ, (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyPB x' x f → KaVal x' n l l' al s' κ' → (κ' : K') = f κ) ∧ ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (f : K →+* K') (x' : KeyIn K') (φ : _) (w : _) (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyVia x' x f φ w ∧ KaVal x' n l l' al s' κ' := by
  intro hL K _ _ _ x n l l' al hA
  obtain ⟨⟨b, hb⟩, hpull⟩ := GlobalTheory.KeyBasis.main hL K x n (by have := hA.1; omega)
  obtain ⟨κ0, hall, hgen⟩ := GlobalTheory.GenericValue.exists_value (K := K)
    (fun (R : Type) [CommRing R] [Algebra K R] (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) =>
      ValAt b l l' al R T a)
    (valAt_map (b := b) hL hA) (valAt_unique (b := b) hL hA) (exists_valAt (b := b) hL hA hb)
    (valAt_generic (b := b) hL hA hb) (valAt_lift (b := b) hL hA)
  obtain ⟨xG, sG, κG, hfG, hkG, hG⟩ := hgen
  have hκ0 : κ0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hG
    exact κG.ne_zero hG.symm
  refine ⟨Units.mk0 κ0 hκ0, ?_, ?_⟩
  · intro K' _ _ f x' s' κ' hx' hk'
    letI : Algebra K K' := f.toAlgebra
    obtain ⟨φ, w, H⟩ := (GlobalTheory.KeyVia.main K K' x x' f).1.1 hx'
    obtain ⟨_, hg, _⟩ := id H
    have M := (GlobalTheory.KeyVia.main K K' x x' f).2 φ w H
    choose b' hb' _ using fun k => M.1 n (b k)
    have hbas : IsBasis x' b' := (hpull b hb K' f x' φ w b' H hb')
    choose c hc _ using fun i : Fin x.P.g => hbas (s' (i.cast hg.symm))
    have hf : Framed b (algebraMap K K') (fun p => c p.1 p.2) x' s' := by
      refine ⟨φ, w, hg, b', H, hb', fun i => ?_⟩
      have e : (i.cast hg).cast hg.symm = i := Fin.ext rfl
      have h1 := hc (i.cast hg)
      rw [e] at h1
      exact h1
    have h2 := hall K' (fun p => c p.1 p.2) κ' ⟨x', s', κ', hf, hk', rfl⟩
    rw [h2, Units.val_mk0]
    rfl
  · obtain ⟨φ, w, hg, b', H, -, -⟩ := hfG
    exact ⟨_, inferInstance, inferInstance, algebraMap K _, xG, φ, w, sG, κG, H, hkG⟩

end GlobalTheory.KaIndep
