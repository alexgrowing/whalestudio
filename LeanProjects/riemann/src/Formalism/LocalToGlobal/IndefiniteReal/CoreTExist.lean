import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.CoreJExistsAt
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.CoreT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Half

theorem span_pair_mul {R : Type} [CommRing R] (p w c m t u v : R) (hw : w ^ 2 = w - m) (ht : c ^ 2 - c + m = p * t)
    (huv : u * (1 - 2 * c) + v * p = 1) : Ideal.span {p, w - c} * Ideal.span {p, 1 - w - c} = Ideal.span {p} := by
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hz with rfl | rfl | rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
    · exact ⟨t, by linear_combination (-1 : R) * hw + ht⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have e : p = u * (p * (1 - w - c)) + u * ((w - c) * p) + v * (p * p) := by linear_combination (-p) * huv
    have key := Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left (Ideal.span {p * p, p * (1 - w - c), (w - c) * p, (w - c) * (1 - w - c)}) u
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      (Ideal.mul_mem_left _ u (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))
      (Ideal.mul_mem_left _ v (Ideal.subset_span (Set.mem_insert _ _)))
    rwa [← e] at key

theorem eq_of_norm {R : Type} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {J J' P : Ideal R} {p : ℕ}
    (hp : p.Prime) (hN : Ideal.absNorm J * Ideal.absNorm J' = p ^ 2) (hJ' : J' ≠ ⊤) (hP : P ≠ ⊤) (hle : J ≤ P) : J = P := by
  obtain ⟨Q, rfl⟩ := Ideal.dvd_iff_le.2 hle
  rw [map_mul] at hN
  have h1 : Ideal.absNorm P ≠ 1 := fun h => hP (Ideal.absNorm_eq_one_iff.1 h)
  have h2 : Ideal.absNorm J' ≠ 1 := fun h => hJ' (Ideal.absNorm_eq_one_iff.1 h)
  have d1 : p ∣ Ideal.absNorm P := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (⟨Ideal.absNorm Q * Ideal.absNorm J', by rw [← hN]; ring⟩ : Ideal.absNorm P ∣ p ^ 2)
    rw [hk] at h1 ⊢
    exact dvd_pow_self p (by rintro rfl; exact h1 rfl)
  have d2 : p ∣ Ideal.absNorm J' := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (⟨Ideal.absNorm P * Ideal.absNorm Q, by rw [← hN]; ring⟩ : Ideal.absNorm J' ∣ p ^ 2)
    rw [hk] at h2 ⊢
    exact dvd_pow_self p (by rintro rfl; exact h2 rfl)
  obtain ⟨a, ha⟩ := d1
  obtain ⟨b, hb⟩ := d2
  have h3 : p ^ 2 * (Ideal.absNorm Q * (a * b)) = p ^ 2 * 1 := by
    rw [ha, hb] at hN
    rw [mul_one]
    calc _ = p * a * Ideal.absNorm Q * (p * b) := by ring
      _ = _ := hN
  have h4 := Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h3)
  rw [Ideal.absNorm_eq_one_iff.1 h4, Ideal.mul_top]

theorem bH_bH (I : Ideal (𝓞 D.host.E)) : (I.map (bH D)).map (bH D) = I := by
  rw [Ideal.map_map]
  have : (bH D).comp (bH D) = RingHom.id _ := RingHom.ext fun a => by
    apply RingOfIntegers.ext
    exact IsCMField.complexConj_apply_apply D.host.E (a : D.host.E)
  rw [this, Ideal.map_id]

theorem span_ne_top {p : ℕ} (hp : p.Prime) : Ideal.span {(p : 𝓞 D.host.E)} ≠ ⊤ := by
  intro h
  have h1 := Ideal.absNorm_span_natCast (S := 𝓞 D.host.E) p
  rw [h, Ideal.absNorm_top] at h1
  rcases Nat.pow_eq_one.1 h1.symm with h2 | h2
  · exact hp.one_lt.ne' h2
  · exact Module.finrank_pos.ne' h2

theorem map_prime {p : ℕ} (hp : SplitOK D p) (P : HeightOneSpectrum (𝓞 D.host.K)) (hP : (p : 𝓞 D.host.K) ∈ P.asIdeal) :
    P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = pIdeal D p ∨
      P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = (pIdeal D p).map (bH D) := by
  have hs : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.subset_adjoin _ _ rfl
  have hw : ((w0E D : 𝓞 D.host.E) : D.host.E) ∈ D.host.K :=
    div_mem (add_mem (one_mem _) hs) (by exact_mod_cast natCast_mem D.host.K 2)
  let w : 𝓞 D.host.K := ⟨⟨(w0E D : D.host.E), hw⟩, (isIntegral_algHom_iff (IntermediateField.val D.host.K).toRingHom.toIntAlgHom
    Subtype.val_injective).1 (w0E D).isIntegral_coe⟩
  have hwE : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) w = w0E D := by
    apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
    rfl
  have hinj : Function.Injective (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := FaithfulSMul.algebraMap_injective _ _
  have hw2 : w ^ 2 = w - (mE D : 𝓞 D.host.K) := hinj (by rw [map_pow, map_sub, map_natCast, hwE, w0E_sq])
  obtain ⟨t, ht⟩ := cRoot_spec D hp
  obtain ⟨u, v, huv⟩ := cRoot_coprime D hp
  have hJ := span_pair_mul (p : 𝓞 D.host.K) w (cRoot D p) (mE D) t u v hw2 (by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) ht)
    (by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) huv)
  have m1 : (Ideal.span {(p : 𝓞 D.host.K), w - (cRoot D p : 𝓞 D.host.K)}).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = pIdeal D p := by
    rw [Ideal.map_span, Set.image_pair, map_natCast, map_sub, hwE, map_intCast, pIdeal]
  have m2 : (Ideal.span {(p : 𝓞 D.host.K), 1 - w - (cRoot D p : 𝓞 D.host.K)}).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) =
      (pIdeal D p).map (bH D) := by
    rw [Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_sub, map_one, hwE, map_intCast, map_pIdeal]
  have n1 : pIdeal D p ≠ ⊤ := fun h => span_ne_top (D := D) hp.1 (by rw [← pIdeal_mul_bar D hp, h, Ideal.map_top, Ideal.top_mul])
  have n2 : (pIdeal D p).map (bH D) ≠ ⊤ := fun h => n1 (by rw [← bH_bH (pIdeal D p), h, Ideal.map_top])
  have hK : Module.finrank ℚ D.host.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (d := D.host.d) D.host.hyp.2.1.pos (D.host.sqd_sq)
  have hN := congrArg Ideal.absNorm hJ
  rw [map_mul, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at hN
  rcases P.isPrime.mul_le.1 (hJ.le.trans ((Ideal.span_singleton_le_iff_mem _).2 hP)) with h | h
  · left
    rw [← m1, eq_of_norm hp.1 hN (fun h' => n2 (by rw [← m2, h', Ideal.map_top])) P.isPrime.ne_top h]
  · right
    rw [← m2, eq_of_norm hp.1 ((mul_comm _ _).trans hN) (fun h' => n1 (by rw [← m1, h', Ideal.map_top])) P.isPrime.ne_top h]

variable (P : Formalism.L2.Host.PiBar D.host)

abbrev hI (k : Fin 2) : Ideal (𝓞 D.host.E) := (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

theorem splitOK_g (k : Fin 2) : SplitOK D (D.host.g k) := ⟨D.host.g_prime k, g_ne_two D k, g_jacobi D k⟩

theorem hI_mul (k : Fin 2) : hI P k * (hI P k).map (bH D) = Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} := by
  rcases map_prime (splitOK_g k) (P.pb k) (P.pb_over k) with h | h
  · rw [hI, h, pIdeal_mul_bar D (splitOK_g k)]
  · rw [hI, h, bH_bH, mul_comm, pIdeal_mul_bar D (splitOK_g k)]

theorem hI_gen (k : Fin 2) : ∃ G : Set (𝓞 D.host.E), hI P k = Ideal.span G ∧ G ⊆ Algebra.adjoin ℤ {w0E D} := by
  have hw : w0E D ∈ Algebra.adjoin ℤ {w0E D} := Algebra.subset_adjoin rfl
  rcases map_prime (splitOK_g k) (P.pb k) (P.pb_over k) with h | h
  · refine ⟨_, h, ?_⟩
    rintro x (rfl | rfl)
    · exact natCast_mem _ _
    · exact sub_mem hw (intCast_mem _ _)
  · refine ⟨_, h.trans (map_pIdeal D _), ?_⟩
    rintro x (rfl | rfl)
    · exact natCast_mem _ _
    · exact sub_mem (sub_mem (one_mem _) hw) (intCast_mem _ _)

theorem hI_cop (k k' : Fin 2) : IsCoprime (hI P k) ((hI P k').map (bH D)) := by
  by_cases hk : k = k'
  · subst hk
    have hc := isCoprime_pq D (splitOK_g k) (splitOK_g k)
    rcases map_prime (splitOK_g k) (P.pb k) (P.pb_over k) with h | h
    · rw [hI, h]; exact hc
    · rw [hI, h, bH_bH]; exact hc.symm
  · have hne : D.host.g k ≠ D.host.g k' := by
      have := D.host.g_ne
      fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hne)
    have huv' : ((u * D.host.g k + v * D.host.g k' : ℤ) : 𝓞 D.host.E) = ((1 : ℤ) : 𝓞 D.host.E) := by rw [huv]
    push_cast at huv'
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ hI P k :=
      (Ideal.mul_le_left : hI P k * (hI P k).map (bH D) ≤ _) (by rw [hI_mul]; exact Ideal.mem_span_singleton_self _)
    have h2 : ((D.host.g k' : ℕ) : 𝓞 D.host.E) ∈ (hI P k').map (bH D) :=
      (Ideal.mul_le_right : hI P k' * (hI P k').map (bH D) ≤ _) (by rw [hI_mul]; exact Ideal.mem_span_singleton_self _)
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, ← huv']
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left h1)) (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right h2))

open Pointwise in

def levelPb : Level (hostOfRecord D) where
  M := D.host.g 0 * D.host.g 1
  three_le := (levelG_M D (unramBridge D.host.E (cmUnram_conj D))).1 ▸ (levelG D).three_le
  odd := (levelG_M D (unramBridge D.host.E (cmUnram_conj D))).1 ▸ (levelG D).odd
  Mb := hI P 0 * hI P 1
  fromK := fromK_of_gen (by
    obtain ⟨G, hG, hA⟩ := hI_gen P 0
    obtain ⟨G', hG', hA'⟩ := hI_gen P 1
    refine ⟨G * G', by rw [hG, hG', Ideal.span_mul_span'], ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (hA ha) (hA' hb))
  prod := by
    show hI P 0 * hI P 1 * (hI P 0 * hI P 1).map (bH D) = _
    rw [Ideal.map_mul, mul_mul_mul_comm, hI_mul, hI_mul, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
  coprime := by
    show hI P 0 * hI P 1 ⊔ (hI P 0 * hI P 1).map (bH D) = ⊤
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.map_mul]
    exact ((hI_cop P 0 0).mul_right (hI_cop P 0 1)).mul_left ((hI_cop P 1 0).mul_right (hI_cop P 1 1))
  A := 1
  A_pos := Nat.one_pos

def parPb (hF : OFull D) (hz : OZeta D) (hN : N1ab) : Par D := parAt D hF hz hN (levelPb P) ⟨rfl, rfl⟩

variable (hF : OFull D) (hz : OZeta D) (hN : N1ab)

def HalfAt (Q : Par D) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧
    Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

end Half

section Chr

def DetChar (V : HSp D) : Prop :=
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, Continuous mu ∧ MuVal V χ mu

theorem mem_of_latHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) {x : Fin n → E}
    (h : (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E))) : x ∈ Λ := by
  have key : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)),
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (y i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hs : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩)
      have hv : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
          Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ := Submodule.subset_span ⟨x, hx, rfl⟩
      convert Submodule.smul_mem _ (⟨(1 : E) ⊗ₜ[F] a, hs⟩ : Formalism.L2.Herm.intAf F E) hv using 1
      funext i
      show Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (a ⊗ₜ[F] x i) =
        ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    | zero =>
      convert Submodule.zero_mem (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ) using 1
      funext i
      exact map_zero _
    | add y z _ _ hy hz =>
      convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    | neg y _ hy =>
      convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  have hg : x ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
        Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    exact key _ h
  rwa [Formalism.UG.P.global_lattice_one_holds F E (Fin n) Λ hfin hsp] at hg

theorem mem_lattice_of_mem_completion (V : HSp D) {v : Fin V.rank → D.host.E} (hv : finVec V v ∈ Formalism.L2.Pj.latHat V) :
    V.frame.equivFun.symm v ∈ V.L0 := by
  let Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL := V.standardTuple_isLattice
  have hfin : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.2 (hL.fg.map _)
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have hle : Formalism.L2.Pj.latHat V ≤ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    AddSubgroup.closure_mono (by
      rintro _ ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, V.frame.equivFun x, ⟨x, hx, rfl⟩, rfl⟩)
  obtain ⟨x, hx, rfl⟩ := mem_of_latHat Λ hfin hsp (hle hv)
  exact (V.frame.equivFun.symm_apply_apply x).symm ▸ hx

abbrev iotaAt {V : HSp D} {r : ℕ} (hr : V.rank = r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι

theorem exists_iota {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {j : ℕ} {Dw : Datum H} (h : IsDatW D j Dw) {r : ℕ}
    (hr : (D.sp.W j).rank = r) : ∃ ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E),
      LatEmb (D.sp.W j) (iotaAt hr ι) ∧ LatIsom (D.sp.W j) Dw.EF (iotaAt hr ι) := by
  subst hr
  obtain ⟨-, -, φ, ε, hφ, hR, hE⟩ := h
  let e := (D.sp.W j).frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)
  refine ⟨e ∘ₗ φ, ⟨(D.sp.W j).frame.equivFun.injective.comp hφ, ?_⟩, ε, fun x y => ?_⟩
  · show LinearMap.range (e ∘ₗ φ) = _
    rw [LinearMap.range_comp, hR, Submodule.map_span, latG]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      refine ⟨a, ha, (D.sp.W j).frame.equivFun x, ⟨finVec _ ((D.sp.W j).frame.equivFun x),
        AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩, ?_⟩, map_smul (D.sp.W j).frame.equivFun a x⟩
      rw [map_one, Units.val_one, Matrix.one_mulVec]
    · rintro ⟨a, ha, v, ⟨z, hz, hv⟩, rfl⟩
      rw [map_one, Units.val_one, Matrix.one_mulVec] at hv
      refine ⟨_, ⟨a, ha, _, mem_lattice_of_mem_completion _ (hv ▸ hz), rfl⟩, ?_⟩
      show (D.sp.W j).frame.equivFun (a • _) = _
      rw [map_smul, LinearEquiv.apply_symm_apply]
  · rw [hE]
    show _ = _ * Algebra.trace ℚ D.host.E (_ * (D.sp.W j).hT ((D.sp.W j).frame.equivFun.symm ((D.sp.W j).frame.equivFun (φ x)))
      ((D.sp.W j).frame.equivFun.symm ((D.sp.W j).frame.equivFun (φ y))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end Chr

section Unif

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

def OrthonormalBaseFrame (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (V : HSp D) (hr : V.rank = r) (q : ℕ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
    ReciprocityTheory.ChartRestriction.G.FD.gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ)

structure UnfLaws (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) : Prop where
  ne : Nonempty U.Comp
  unf : IsUnf U
  unTest : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)
  chiTriv : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1
  rdIndep : RdIndep1 U

  holFD : HolomorphicSectionsFinDim U
  rdDomInj : RdDomInj1 U
  modelW : ∀ k, ModelW V hr (U.X k)

def LatDict (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U V hr dict ι e F ik φ th x₀

structure DictLaws (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) (Kf : Subgroup (GA D V))
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) : Prop where
  dictU : ∃ th, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr
  unitFr : ∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1
  adelMeas : AdelMeas1 U V dict 1
  aeDom : AeDom1 U V dict 1
  lat : LatDict U V hr dict ι x₀

variable (Xo c σ) in

def FamAt : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty →
    Nonempty (FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)

variable (Xo c σ) in

def UnifEx (V : HSp D) (hr : V.rank = r) (Kf : Subgroup (GA D V)) (Ex : Unf Xo c σ r → Prop) : Prop :=
  FamAt Xo c σ → ∃ U : Unf Xo c σ r, UnfLaws U V hr ∧ Ex U ∧
    ∀ ι, LatEmb V ι → LatIsom V Dw.EF ι → ∀ x₀, OrthonormalBaseFrame H V hr Dw.q x₀ → ∃ dict, DictLaws U V hr Kf ι x₀ dict

variable {U : Unf Xo c σ r} {V : HSp D} {dict : GA D V → Σ k, Frame (U.X k).Ψ r} {mu : GA D V → ℂ}

end Unif

section Core

theorem rankW {j : ℕ} (hj : InR D j) : (D.sp.W j).rank = D.R.r := D.sp.W_rank j hj.1 hj.2

abbrev kW (D : D7) (j : ℕ) : Subgroup (GA D (D.sp.W j)) := kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)

structure CoreIn (Q : Par D) (Ex : ∀ j (σ : Q.c.F →+* ℂ), Unf (Q.Xo j) Q.c σ D.R.r → Prop) : Prop where

  frChart : ∀ j, InR D j → FrChartF (Q.Xo j) Q.c
  borChart : ∀ j, InR D j → BorChartF (Q.Xo j) Q.c
  intLatU : ∀ j, InR D j → IntLatU (Q.Xo j) Q.c

  algPtLa : ∀ j, InR D j → AlgPtLa (Q.Xo j) Q.c
  intFrExt : ∀ j, InR D j → IntFrExt (Q.Xo j) Q.c
  intAll : ∀ j, InR D j → Formalism.L2.Pj.IntAll (Q.Xo j) Q.c

  volTie : VolTieG D

  levGrp : ∀ j, InR D j → LevGrp (D.sp.W j) (D.host.g 0 * D.host.g 1)
  kfHalf : ∀ j, InR D j → KfHalf (D.sp.W j) (kW D j) Q.l.M (Q.l.Mb.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

  detChar : ∀ j, InR D j → DetChar (D.sp.W j)

  unif : ∀ j (hj : InR D j) σ, GoodEmb Q.c σ → UnifEx (Q.Xo j) Q.c σ (D.sp.W j) (rankW hj) (kW D j) (Ex j σ)

  ptEx : ∀ j (σ : Q.c.F →+* ℂ), Nonempty (FrPt (Q.Xo j) Q.c (CAt σ))

variable (Q : Par D)

abbrev mkJ (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) (U : ∀ j (σ : Q.c.F →+* ℂ), Unf (Q.Xo j) Q.c σ D.R.r)
    (dict : ∀ j σ, GA D (D.sp.W j) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j (_ : Q.c.F →+* ℂ), GA D (D.sp.W j) → ℂ)
    (cE : ∀ j σ, (U j σ).Comp → ℂ) (χ : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle)
    (x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (ι : ∀ j, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : CoreJ D where
  Q := Q
  U := U
  V j _ := D.sp.W j
  dict := dict
  mu := mu
  Kf j _ := kW D j
  pb := pb
  cE := cE
  chiW := χ
  x₀ := x₀
  iota := ι

def ChiOK (χ : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) : Prop :=
  ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → IsHeckeChar D (χ j σ) ∧ (∀ a, χ j σ (idF D a) = 1) ∧
    MuConj Q.c.F.val.toRingHom σ (χ j Q.c.F.val.toRingHom) (χ j σ)

def AdmissibleBaseFrames (x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop :=
  ∀ j (hj : InR D j) σ, GoodEmb Q.c σ → OrthonormalBaseFrame Q.H (D.sp.W j) (rankW hj) (Q.Dw j).q (x₀ j σ)

def IotaOK (ι : ∀ j, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  ∀ j (hj : InR D j), LatEmb (D.sp.W j) (iotaAt (rankW hj) (ι j)) ∧ LatIsom (D.sp.W j) (Q.Dw j).EF (iotaAt (rankW hj) (ι j))

variable {Q}

def CuspEx (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (U : Unf (Q.Xo j) Q.c σ D.R.r) : Prop :=
  FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

abbrev setCE (T : CoreJ D) (c : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D := { T with cE := c }

end Core

section Rec

variable (Q : Par D)

def HeckeConj : Prop :=
  ∀ (χ₀ : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), IsHeckeChar D χ₀ → (∀ x, χ₀ (idF D x) = 1) → (∀ ρ, HasInfExp D χ₀ ρ (a ρ)) →
    (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = (y : ℂ)) →
    ∀ σ : Q.c.F →+* ℂ, GoodEmb Q.c σ → ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ (∀ x, χ (idF D x) = 1) ∧
      (∀ ρ ρ', relab Q.c σ (tauE D ρ') = tauE D ρ → HasInfExp D χ ρ (a ρ')) ∧
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = (y : ℂ) ∧ ((χ x : Circle) : ℂ) = σ y

variable (D) in

def Mu0Inf (mu0 : ℕ → (AE D)ˣ →* Circle) : Prop :=
  ∀ i : Fin D.R.m, IsHeckeChar D (mu0 ((i : ℕ) + 1)) ∧ (∀ x, mu0 ((i : ℕ) + 1) (idF D x) = 1) ∧
    ∀ ρ, HasInfExp D (mu0 ((i : ℕ) + 1)) ρ (-(D.hc ρ).e i)

variable (D) in

def Mu0Val (mu0 : ℕ → (AE D)ˣ →* Circle) : Prop :=
  ∀ (i : Fin D.R.m) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → ((mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ FO D

def ChiFam (mu0 : ℕ → (AE D)ˣ →* Circle) (χ : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) : Prop :=
  ∀ i : Fin D.R.m, χ ((i : ℕ) + 1) Q.c.F.val.toRingHom = mu0 ((i : ℕ) + 1) ∧ ∀ σ, GoodEmb Q.c σ →
    IsHeckeChar D (χ ((i : ℕ) + 1) σ) ∧ (∀ x, χ ((i : ℕ) + 1) σ (idF D x) = 1) ∧
      (∀ ρ ρ', relab Q.c σ (tauE D ρ') = tauE D ρ → HasInfExp D (χ ((i : ℕ) + 1) σ) ρ (-(D.hc ρ').e i)) ∧
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 →
        ∃ y : Q.c.F, ((mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = (y : ℂ) ∧ ((χ ((i : ℕ) + 1) σ x : Circle) : ℂ) = σ y

variable {Q}

end Rec

section Pg

end Pg

section Rows

section Gen

variable {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (s : E →ₐ[F] E)
  (hs : ∀ e, ∃ f : F, algebraMap F E f = e + s e)

include hs

end Gen

section H90

end H90

def MuCont (V : HSp D) : Prop := ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → Continuous (muOf V χ)

theorem iotaEx_of {Q : Par D} (hQ : Q.Pins) (j : ℕ) (hj : InR D j) : IotaEx Q j hj := exists_iota (hQ.2.2.2 j hj) (rankW hj)

structure RowsIn (hN : N1c) (Q : Par D) (hQ : Q.Pins) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) : Prop where
  frChart : ∀ j, InR D j → FrChartF (Q.Xo j) Q.c
  borChart : ∀ j, InR D j → BorChartF (Q.Xo j) Q.c
  intLatU : ∀ j, InR D j → IntLatU (Q.Xo j) Q.c
  allTest : ∀ j, InR D j → AllTest (Q.Xo j) Q.c
  bcEx : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → BCEx (Q.Xo j) Q.c σ
  algPtLa : ∀ j, InR D j → AlgPtLa (Q.Xo j) Q.c
  intFrExt : ∀ j, InR D j → IntFrExt (Q.Xo j) Q.c
  intAll : ∀ j, InR D j → Formalism.L2.Pj.IntAll (Q.Xo j) Q.c
  m5 : SiegelSpaceAlgebra (E := D.host.E)
  volTie : VolTieG D
  levGrp : ∀ j, InR D j → LevGrp (D.sp.W j) (D.host.g 0 * D.host.g 1)
  kfHalf : ∀ j, InR D j → KfHalf (D.sp.W j) (kW D j) Q.l.M (Q.l.Mb.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))
  muCont : ∀ j, InR D j → MuCont (D.sp.W j)

  pkg : ∀ j (hj : InR D j) σ (hσ : GoodEmb Q.c σ), V3.PkgRows hN Q hpq (infPlaceEx_holds D) j hj (iotaEx_of hQ j hj) σ hσ 1
  ptEx : ∀ j (σ : Q.c.F →+* ℂ), Nonempty (FrPt (Q.Xo j) Q.c (CAt σ))

end Rows

section Cover

open CategoryTheory

attribute [local instance] Over.cartesianMonoidalCategory

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

abbrev idCov (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) (n : ℕ) : DeltaDat Xo c n where
  pd := 1
  I := ⊤
  l₂ := l
  Xo₂ := Xo
  c₂ := c
  hF := rfl
  r := 𝟙 _
  m := m
  nab₂ := nab
  cδ := 1
  φδ := fun _ => 1

def IdCov : Prop :=
  ∃ m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X), m.φ = 𝟙 _ ∧
    ∀ (nab : NabV Xo c) (n : ℕ) (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k), FrOver (idCov Xo c nab m n) y y

def NabEx : Prop := ∃ (nab : NabV Xo c) (_ : StarRing (𝓞 D.host.E)), IsNab Xo c nab

def LevHom (l : Level H) {G : Type} [Group G] (lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La) : Prop :=
  (∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) ∧
    ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)

def ActGeo : Prop :=
  ∀ (G : Type) [Group G] (lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La), LevHom l lev →
    ActLev (Xo := Xo) c fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))

variable {Xo c}

end Cover

section IdMap

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

section Cech

variable {X Y : Scheme.{0}}

theorem rs_rs {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h (ReciprocityTheory.ChartRestriction.G.Semi.res h' x) = ReciprocityTheory.ChartRestriction.G.Semi.res (h.trans h') x := by
  ext
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rs_pull_rs (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h' : U' ≤ U) (h : V ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h (pullU f U' (ReciprocityTheory.ChartRestriction.G.Semi.res h' x)) = ReciprocityTheory.ChartRestriction.G.Semi.res (h.trans (fun _ hy => h' hy)) (pullU f U x) := by
  ext
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, pullU, Units.coe_map, MonoidHom.coe_coe]
  have e1 : f.appLE U V (h.trans (fun _ hy => h' hy)) = X.presheaf.map (homOfLE h').op ≫ f.appLE U' V h :=
    (Scheme.Hom.map_appLE f h (homOfLE h').op).symm
  exact (congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, V) => φ.hom x) e1).symm

theorem cocyc {L : LB X} (hL : L.IsLB) {V : X.Opens} (i j k : L.ι) (hij : V ≤ L.U i ⊓ L.U j) (hjk : V ≤ L.U j ⊓ L.U k)
    (hik : V ≤ L.U i ⊓ L.U k) : ReciprocityTheory.ChartRestriction.G.Semi.res hij (L.g i j) * ReciprocityTheory.ChartRestriction.G.Semi.res hjk (L.g j k) = ReciprocityTheory.ChartRestriction.G.Semi.res hik (L.g i k) := by
  have h := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res (le_inf hij (hjk.trans inf_le_right))) (hL.cocycle i j k)
  rwa [map_mul, rs_rs, rs_rs, rs_rs] at h

variable (L : LB X)

theorem idU_le (a : PUnit → L.ι) : (L.pull (𝟙 X)).U a ≤ L.U (a ⟨⟩) := LB.wchart_le L (fun _ : PUnit => 𝟙 X) a ⟨⟩

theorem idG (a b : PUnit → L.ι) :
    (L.pull (𝟙 X)).g a b = ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf (idU_le L a) (idU_le L b)) (L.g (a ⟨⟩) (b ⟨⟩)) :=
  (Fintype.prod_unique (fun _ : PUnit => ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf (idU_le L a) (idU_le L b)) (L.g (a ⟨⟩) (b ⟨⟩)) ^ (1 : ℤ))).trans (zpow_one _)

theorem coc4 (hL : L.IsLB) {V : X.Opens} (a i b j : L.ι) (hai : V ≤ L.U a ⊓ L.U i) (hab : V ≤ L.U a ⊓ L.U b)
    (hij : V ≤ L.U i ⊓ L.U j) (hbj : V ≤ L.U b ⊓ L.U j) :
    ReciprocityTheory.ChartRestriction.G.Semi.res hai (L.g a i) = ReciprocityTheory.ChartRestriction.G.Semi.res hab (L.g a b) * (ReciprocityTheory.ChartRestriction.G.Semi.res hij (L.g i j))⁻¹ * ReciprocityTheory.ChartRestriction.G.Semi.res hbj (L.g b j) := by
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq, cocyc hL a i j hai hij (le_inf (hai.trans inf_le_left) (hij.trans inf_le_right)),
    cocyc hL a b j hab hbj]

def idIso : LB.Iso L (L.pull (𝟙 X)) where
  s p := ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf (idU_le L p.1) le_rfl) (L.g (p.1 ⟨⟩) p.2)

theorem idIso_gen (hL : L.IsLB) : (idIso L).IsGen := fun p q =>
  (rs_rs _ _ _).trans ((coc4 L hL (p.1 ⟨⟩) p.2 (q.1 ⟨⟩) q.2 _ _ _ _).trans
    (congrArg₂ (· * ·) (congrArg (· * _) ((congrArg _ (idG L p.1 q.1)).trans (rs_rs _ _ _)).symm) (rs_rs _ _ _).symm))

variable {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem combU_le (j : K → PUnit → L.ι) : (LB.LinComb (L.pull (𝟙 X)) φ ε).U j ≤ (LB.LinComb L φ ε).U (fun k => j k ⟨⟩) :=
  fun _ hy => Set.mem_iInter.2 fun k => idU_le L (j k) (Set.mem_iInter.1 hy k)

omit L in
theorem prod_rs {V W : Y.Opens} (h : W ≤ V) (U U' : K → X.Opens) (hU : ∀ k, U' k ≤ U k) (hW : ∀ k, W ≤ φ k ⁻¹ᵁ U' k)
    (hV : ∀ k, V ≤ φ k ⁻¹ᵁ U k) (x : ∀ k, Γ(X, U k)ˣ) :
    ∏ k, ReciprocityTheory.ChartRestriction.G.Semi.res (hW k) (pullU (φ k) (U' k) (ReciprocityTheory.ChartRestriction.G.Semi.res (hU k) (x k))) ^ ε k = ReciprocityTheory.ChartRestriction.G.Semi.res h (∏ k, ReciprocityTheory.ChartRestriction.G.Semi.res (hV k) (pullU (φ k) (U k) (x k)) ^ ε k) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, rs_rs, rs_pull_rs]

theorem combIso (p : (K → PUnit → L.ι) × (K → L.ι)) :
    @id (Γ(Y, (LB.LinComb (L.pull (𝟙 X)) φ ε).U p.1 ⊓ (LB.LinComb L φ ε).U p.2)ˣ) ((LB.linCombIso (idIso L) φ ε).s p) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf (combU_le L φ ε p.1) le_rfl) ((LB.LinComb L φ ε).g (fun k => p.1 k ⟨⟩) p.2) :=
  prod_rs φ ε (inf_le_inf (combU_le L φ ε p.1) le_rfl) (fun k => L.U (p.1 k ⟨⟩) ⊓ L.U (p.2 k))
    (fun k => (L.pull (𝟙 X)).U (p.1 k) ⊓ L.U (p.2 k)) (fun k => inf_le_inf (idU_le L (p.1 k)) le_rfl)
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le (L.pull (𝟙 X)) φ p.1 k)) (inf_le_right.trans (LB.wchart_le L φ p.2 k)))
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ (fun k => p.1 k ⟨⟩) k)) (inf_le_right.trans (LB.wchart_le L φ p.2 k)))
    (fun k => L.g (p.1 k ⟨⟩) (p.2 k))

theorem combG (j j' : K → PUnit → L.ι) : (LB.LinComb (L.pull (𝟙 X)) φ ε).g j j' =
    ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf (combU_le L φ ε j) (combU_le L φ ε j')) ((LB.LinComb L φ ε).g (fun k => j k ⟨⟩) (fun k => j' k ⟨⟩)) :=
  have hW : ∀ k, (LB.LinComb (L.pull (𝟙 X)) φ ε).U j ⊓ (LB.LinComb (L.pull (𝟙 X)) φ ε).U j' ≤
      φ k ⁻¹ᵁ ((L.pull (𝟙 X)).U (j k) ⊓ (L.pull (𝟙 X)).U (j' k)) := fun k =>
    le_inf (inf_le_left.trans (LB.wchart_le (L.pull (𝟙 X)) φ j k)) (inf_le_right.trans (LB.wchart_le (L.pull (𝟙 X)) φ j' k))
  (Finset.prod_congr rfl fun k _ => congrArg (fun z => ReciprocityTheory.ChartRestriction.G.Semi.res (hW k) (pullU (φ k) _ z) ^ ε k) (idG L (j k) (j' k))).trans
    (prod_rs φ ε (inf_le_inf (combU_le L φ ε j) (combU_le L φ ε j')) (fun k => L.U (j k ⟨⟩) ⊓ L.U (j' k ⟨⟩))
      (fun k => (L.pull (𝟙 X)).U (j k) ⊓ (L.pull (𝟙 X)).U (j' k)) (fun k => inf_le_inf (idU_le L (j k)) (idU_le L (j' k))) hW
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ (fun k => j k ⟨⟩) k))
        (inf_le_right.trans (LB.wchart_le L φ (fun k => j' k ⟨⟩) k)))
      (fun k => L.g (j k ⟨⟩) (j' k ⟨⟩)))

theorem maps_id (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb (L.pull (𝟙 X)) φ ε))
    (h : ∀ j, t'.s j = ReciprocityTheory.ChartRestriction.G.Semi.res (combU_le L φ ε j) (t.s fun k => j k ⟨⟩)) : LB.Gen.Maps (LB.linCombIso (idIso L) φ ε) t t' := by
  intro p
  have e := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf (combU_le L φ ε p.1) (le_refl ((LB.LinComb L φ ε).U p.2)))) (ht (fun k => p.1 k ⟨⟩) p.2)
  rw [map_mul, rs_rs, rs_rs] at e
  erw [h, rs_rs, combIso]
  exact e

theorem rg_rg {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE h').op).hom x) = (X.presheaf.map (homOfLE (h.trans h')).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def secId (s : LB.Sec (LB.LinComb L φ ε)) : LB.Sec (LB.LinComb (L.pull (𝟙 X)) φ ε) where
  f j := (Y.presheaf.map (homOfLE (combU_le L φ ε j)).op).hom (s.f fun k => j k ⟨⟩)
  compat j j' := by
    have e := congrArg (Y.presheaf.map (homOfLE (inf_le_inf (combU_le L φ ε j) (combU_le L φ ε j'))).op).hom
      (s.compat (fun k => j k ⟨⟩) (fun k => j' k ⟨⟩))
    rw [map_mul, rg_rg, rg_rg] at e
    erw [combG, rg_rg, rg_rg]
    exact e

end Cech

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

open scoped MonObj in

def idSAB {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm :=
    { F := 𝟙 _
      F3 := 𝟙 _
      e := 𝟙 _
      e_comm := (Category.comp_id _).trans (Category.id_comp _).symm
      psum_comm := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm }
  cart := ⟨IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩, fun T x y x₀ y₀ hx hy => by
    let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    have ex : x₀ = u ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    have ey : y₀ = u ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    rw [ex, ey, ← MonObj.comp_mul]
    exact (Category.id_comp _).trans (Category.comp_id _).symm⟩
  base := rfl
  act _ := (Category.comp_id _).trans (Category.id_comp _).symm
  lin := ⟨idIso t.PP.L, idIso_gen _ t.PP.isLB, maps_id _ _ _ _ t.PP.rigGen _ fun _ => rfl, maps_id _ _ _ _ t.cub.isGen _ fun _ => rfl⟩

end IdMap

section Trans

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

include hle

end Trans

section Lat

variable {n : ℕ}

def conjLat (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : GenLat D.host.E n where
  La :=
    { carrier := {v | (fun j => IsCMField.complexConj D.host.E (v j)) ∈ L}
      add_mem' := fun {v w} hv hw => by
        have e : (fun j => IsCMField.complexConj D.host.E ((v + w) j)) =
            (fun j => IsCMField.complexConj D.host.E (v j)) + fun j => IsCMField.complexConj D.host.E (w j) :=
          funext fun j => map_add _ _ _
        exact (congrArg (· ∈ L) e).mpr (L.add_mem hv hw)
      zero_mem' := by
        show (fun j => IsCMField.complexConj D.host.E ((0 : Fin n → D.host.E) j)) ∈ L
        simp only [Pi.zero_apply, map_zero]
        exact L.zero_mem
      smul_mem' := fun a v hv => by
        have h := L.smul_mem (barE D a) hv
        have e : (fun j => IsCMField.complexConj D.host.E ((a • v) j)) = barE D a • fun j => IsCMField.complexConj D.host.E (v j) :=
          funext fun j => map_mul (IsCMField.complexConj D.host.E) (a : D.host.E) (v j)
        exact (congrArg (· ∈ L) e).mpr h }

def RepsLat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (i : Fin D.R.m) : Prop :=
  VStd D i → ∀ (bad : ℕ) (h : GA D (Vc D i)), bad ≠ 0 → SplitOffBad (Vc D i) bad h →
    (conjLat (Bridge.hLat (Vc D i) (fin _ h))).Unimod ∧ (conjLat (Bridge.hLat (Vc D i) (fin _ h))).TrivAt bad ∧
      GenLat.SplitSupp H (conjLat (Bridge.hLat (Vc D i) (fin _ h)))

def EpSq (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (n r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (cc : Ideal (𝓞 D.host.E)),
    (⟨L⟩ : GenLat D.host.E n).Unimod → GenLat.SplitSupp H (⟨L⟩ : GenLat D.host.E n) →
    cc ⊔ cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ →
    Submodule.span (𝓞 D.host.E) (detSet L) * idlE (cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) = idlE cc →
    ∃ q : ℚ, 0 < q ∧ q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r =
      (Ideal.absNorm cc : ℚ)

end Lat

section OM

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (D) in

abbrev LLc : IntermediateField ℚ ℂ := D.what₂.embLL.toRatAlgHom.fieldRange

variable (D) in

def jLL : D.what₂.LL →+* LLc D := (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toRingEquiv.toRingHom

theorem F_le {Q : Par D} (hp : Q.PinField) : Q.c.F ≤ LLc D := fun z hz => by
  obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)
  have e : z = ((x : Q.c.F) : ℂ) / ((y : Q.c.F) : ℂ) := (congrArg Subtype.val h).symm
  rw [e, ← hp, ← hp]
  exact div_mem ⟨_, rfl⟩ ⟨_, rfl⟩

abbrev coeffLL {Q : Par D} (hp : Q.PinField) : Coeff Q.l where
  F := LLc D
  fin := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv
  conj τ a := F_le hp (Q.c.conj τ a)
  zeta_mem := F_le hp Q.c.zeta_mem
  le := Q.c.le.trans (F_le hp)

structure OMIn (Q : Par D) (c' : Coeff Q.l) (hle : Q.c.F ≤ c'.F) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) : Prop where

  allTest : AllTest (Q.Xo ((i : ℕ) + 1)) c'

  nab : NabEx (Q.Xo ((i : ℕ) + 1)) Q.c

  act : ActGeo (Q.Xo ((i : ℕ) + 1)) Q.c

  secBC : SecBC (Q.Xo ((i : ℕ) + 1)) hle

  reps : RepsLat Q.H i
  ep : EpSq Q.H (Vc D i).rank ((Q.Dw ((i : ℕ) + 1)).p + (Q.Dw ((i : ℕ) + 1)).q)

  io : ∃ io hw, IoLFRec (Dw := Q.Dw ((i : ℕ) + 1)) c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA κ) io hw

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec)
  (c' : Coeff T.Q.l) (jL : D.what₂.LL →+* c'.F) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)

def RSide : Prop :=
  LevHom T.Q.l lev ∧ ∃ (c0' : VsV D i c'.F →ₛₗ[inC c'] (R.cV i).W) (Cl : Type) (_ : Fintype Cl) (bad : ℕ)
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : c'.F) (B : Ideal (𝓞 D.host.E) → c'.F)
    (φ : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) T.Q.l) → c'.F) (thAd : (Cl → VsV D i c'.F) → AutQ (Wc D i) → ℂ)
    (Plc : (Cl → VsV D i c'.F) → Prop),
    ThPinsR R i jL (inC c') v₀ c0' (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev ∧
      ThPinsT R i (inC c') A.μ0 v₀ c0' (iotaW T i) bad T.Q.l.Mb ⊤ (Mfr T.Q.l • ⊤) Lh gam vol B 1 φ thAd Plc ∧
      BadPin bad (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) ∧ ∀ k, 0 < gam k

variable {T R i v₀ c' jL lev}

end OM

end Formalism.IndefR.CoreT
