import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdmissibleFalseIffFirstInvariant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortValueCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.GenusLatCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem isTwoLifts_iff {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (N : ℕ) {T : Over X}
    (s : LB.Sec (LPow A L.L 1 T)) (x₁ x₂ : T ⟶ A) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) :
    IsTwoLifts A L N s x₁ x₂ F ↔ Odd N ∧ x₁ ^ (N ^ 2) = 1 ∧ x₂ ^ (N ^ 2) = 1 ∧ IsUUOver A L N s x₁ x₂ F := by
  refine and_congr_right' (and_congr_right' (and_congr_right' ⟨?_, ?_⟩))
  · rintro ⟨α₀, α, s₁, s₂, U₁, U₂, g₀, n₀, -, h⟩
    exact ⟨α₀, α, s₁, s₂, U₁, U₂, g₀, n₀, h⟩
  · rintro ⟨α₀, α, s₁, s₂, U₁, U₂, g₀, n₀, cα, tw, h⟩
    obtain ⟨β, gβ, cβ⟩ := NormMulUniv.exists_pull L.isLB α₀ g₀ T
    obtain ⟨r, tr, -⟩ := existsUnique_isTwistPull _ _ _ L.isLB T (mulT A T N) (snd T A ^ N)
      (lift_snd _ _) ((N : ℤ) ^ 2) 1 β gβ s
    obtain rfl : s₁ = r := TranslExist.twist_congr L.isLB
      (fun y J hJ => (val_corr hJ cα _).trans (val_corr hJ cβ _).symm) tw tr
    exact ⟨α₀, β, s₁, s₂, U₁, U₂, g₀, n₀, gβ, cβ, tr, h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

omit [IsCMField E] in

theorem hom_eq_sum {n N : ℕ} {Lm : Submodule (𝓞 E) (Fin n → E)}
    (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Lm) (f : Lm →ₗ[𝓞 E] 𝓞 E) (v : Lm) :
    (N : E) * (f v : E) = ∑ j, (f ⟨_, hN j⟩ : E) * v.1 j := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) v.1
  choose u hu using hd
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using nonZeroDivisors.ne_zero d.2
  have h1 : ((d : 𝓞 E) * N) • v = ∑ j, u j • (⟨_, hN j⟩ : Lm) := by
    apply Subtype.ext
    funext b
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj.symm]) (by simp)]
    simp only [Algebra.smul_def, hu, Pi.single_eq_same, map_mul, map_natCast, eq_natCast, Nat.cast_id]
    ring
  have h2 := congrArg (fun z => algebraMap (𝓞 E) E (f z)) h1
  simp only [map_smul, map_sum, smul_eq_mul, map_mul, map_natCast, hu] at h2
  apply mul_left_cancel₀ hd0
  rw [← _root_.mul_assoc, Finset.mul_sum]
  refine h2.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Algebra.smul_def]
  simp only [RingOfIntegers.coe_eq_algebraMap]
  ring

theorem inZh_iff_inKer {n N : ℕ} (hN0 : N ≠ 0) (Γ : GenLat E n)
    (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Γ.La) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) :
    InZh Xo Γ N a ↔ InKer Xo N Γ.La hN a := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN0
  refine and_congr_right' ⟨fun h f i => ?_, fun h mu hmu cm hcm i => ?_⟩
  · rw [← List.prod_ofFn]
    refine h (Matrix.of fun i j => (f ⟨_, hN j⟩ i : E) / N) (fun v hv => mem_stdMod.2 fun b => ⟨f ⟨v, hv⟩ b, ?_⟩)
      (fun i j => f ⟨_, hN j⟩ i) (fun i j => by simp only [Matrix.of_apply]; field_simp) i
    apply mul_left_cancel₀ hNE
    refine (hom_eq_sum hN (LinearMap.proj b ∘ₗ f) ⟨v, hv⟩).trans ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (f ⟨_, hN j⟩ b : E) * v j = _
    field_simp
  · choose g hg using fun v : Γ.La => mem_stdMod.1 (hmu v.1 v.2)
    let f : Γ.La →ₗ[𝓞 E] (Fin n → 𝓞 E) :=
      { toFun := g
        map_add' := fun v w => funext fun b => RingOfIntegers.ext (by
          change _ = ((g v b : E) + g w b)
          rw [hg, hg, hg, Submodule.coe_add, Matrix.mulVec_add, Pi.add_apply])
        map_smul' := fun o v => funext fun b => RingOfIntegers.ext (by
          change _ = ((o : E) * g v b)
          rw [hg, hg, Submodule.coe_smul, ← algebraMap_smul E, Matrix.mulVec_smul]
          rfl) }
    have hf : ∀ j, cm i j = f ⟨_, hN j⟩ i := fun j => RingOfIntegers.ext (by
      change _ = (g _ i : E)
      rw [hg, hcm, Matrix.mulVec_smul, Matrix.mulVec_single_one]
      simp)
    rw [List.prod_ofFn]
    simpa only [hf] using h f i

theorem inZh_iff {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X}
    (a : Fin n → (T ⟶ Xo.univ.t.G)) : InZh Xo (toGen Λ) N a ↔ InZ Xo h a :=
  inZh_iff_inKer Xo h.1.pos.ne' (toGen Λ) (nsmul_single_mem h) a

omit [IsCMField E] in
theorem exists_pow_le_halfPart' (I : Ideal (𝓞 E)) {N : ℕ} (hN : N ≠ 0) :
    ∃ k : ℕ, I ^ k ≤ ⨅ m : ℕ, Ideal.span {(N : 𝓞 E)} ⊔ I ^ m := by
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  let π := Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})
  obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes (R := 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})
    (M := 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})
    ⟨fun m => OrderDual.toDual ((I ^ m).map π), fun a b hab => Ideal.map_mono (Ideal.pow_le_pow_right hab)⟩
  refine ⟨k, le_iInf fun m => ?_⟩
  rcases le_total m k with hm | hm
  · exact (Ideal.pow_le_pow_right hm).trans le_sup_right
  · have h1 : (I ^ k).map π = (I ^ m).map π := hk m hm
    refine Ideal.le_comap_map.trans (le_of_eq (b := _) (a := ((I ^ k).map π).comap π) ?_)
    rw [h1, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_comm]

def ann {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) : Ideal (𝓞 E) where
  carrier := {a | t ≫ Xo.univ.t.act.act a = 1}
  add_mem' := fun {a b} ha hb => by
    change t ≫ _ = 1
    rw [Xo.univ.t.act.add, MonObj.comp_mul, ha, hb, _root_.mul_one]
  zero_mem' := by
    change t ≫ _ = 1
    rw [← Nat.cast_zero, ZhStable.act_natCast, pow_zero, MonObj.comp_one]
  smul_mem' := fun r a ha => by
    have := Xo.univ.t.act.hom r
    change t ≫ _ = 1
    rw [smul_eq_mul, mul_comm, Xo.univ.t.act.mul, ← Category.assoc, ha, MonObj.one_comp]

theorem isDivPt_iff {N : ℕ} (hN : N ≠ 0) {T : Over Xo.X} {t : T ⟶ Xo.univ.t.G} (ht : t ^ N = 1)
    (t' : T ⟶ Xo.univ.t.G) : (t' ^ N = t ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) t') ↔ IsDivPt Xo N t t' := by
  refine and_congr_right fun h => ⟨fun ⟨j, hj⟩ => ?_, fun hk => ?_⟩
  · have h1 : l.Mb ^ j ≤ ann Xo t' := hj
    have h2 : (N : 𝓞 E) * N ∈ ann Xo t' := by
      change t' ≫ _ = 1
      rw [← Nat.cast_mul, ZhStable.act_natCast, MonObj.comp_pow, Category.comp_id, pow_mul, h, ht]
    have h3 : halfPart l N ≤ Ideal.span {(N : 𝓞 E)} ⊔ ann Xo t' :=
      (iInf_le _ j).trans (sup_le_sup_left h1 _)
    change halfPart l N ^ 2 ≤ ann Xo t'
    refine (Ideal.pow_right_mono h3 2).trans ?_
    rw [sq, Ideal.sup_mul, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    exact sup_le (sup_le ((Ideal.span_singleton_le_iff_mem _).2 h2) Ideal.mul_le_right) Ideal.mul_le_left
  · obtain ⟨k, hk'⟩ := exists_pow_le_halfPart' l.Mb hN
    exact ⟨k * 2, fun a ha => hk a (Ideal.pow_right_mono hk' 2 (pow_mul l.Mb k 2 ▸ ha))⟩

theorem levPtCl_pow {N : ℕ} (hN : l.M ∣ N) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (q : NamedCl Dw l) :
    levPtCl Xo x0 q ^ N = 1 := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨k, rfl⟩ := hN
  rw [levPtCl_mk, levPt, pow_mul, ← MonObj.comp_pow, LevelPoints.eta_pow, MonObj.comp_one, one_pow]

omit [NumberField E] [IsCMField E] in
theorem mem_of_forall_prime {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ p : ℕ, p.Prime → ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L) : x ∈ L := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ k • x ∈ L := by
    obtain ⟨k, hk, hx⟩ := h 2 Nat.prime_two
    exact ⟨k, Nat.pos_of_ne_zero fun e => hk (e ▸ dvd_zero 2), hx⟩
  obtain ⟨hd, hx⟩ := Nat.find_spec hex
  by_cases h1 : Nat.find hex = 1
  · rwa [h1, one_smul] at hx
  obtain ⟨k, hk, hkx⟩ := h _ (Nat.minFac_prime h1)
  refine absurd ((Nat.minFac_dvd _).trans ?_) hk
  by_contra hnd
  refine Nat.find_min hex (Nat.mod_lt k hd) ⟨Nat.pos_of_ne_zero fun e => hnd (Nat.dvd_of_mod_eq_zero e), ?_⟩
  have : (k % Nat.find hex) • x = k • x - (k / Nat.find hex) • Nat.find hex • x := by
    rw [eq_sub_iff_add_eq, smul_smul, ← add_smul, Nat.mod_add_div']
  rw [this]
  exact L.sub_mem hkx (nsmul_mem hx _)

theorem stdForm_nsmul {n : ℕ} (a b : ℕ) (x y : Fin n → E) : stdForm (a • x) (b • y) = (a * b) • stdForm x y := by
  simp only [stdForm, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum, Nat.cast_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem selfDual_of_inGenus {n : ℕ} {Λ : Lat E n} (h : Λ.InGenus) : Λ.SelfDual := by
  classical
  refine fun x => ⟨fun hx y hy => ?_, fun hx => mem_of_forall_prime _ _ fun p hp => ?_⟩
  · have := mem_of_forall_prime (stdMod E 1) (fun _ => stdForm x y) fun p hp => by
      obtain ⟨g, hg, h1, -⟩ := h p hp
      obtain ⟨a, ha, x', hx', ex⟩ := h1 x hx
      obtain ⟨b, hb, y', hy', ey⟩ := h1 y hy
      obtain ⟨o, ho⟩ := (std_selfDual x').1 hx' y' hy'
      refine ⟨a * b, fun hd => (hp.dvd_mul.1 hd).elim ha hb, mem_stdMod.2 fun _ => ⟨o, ?_⟩⟩
      rw [ho, ← hg]
      exact (congrArg₂ stdForm ex ey).trans (stdForm_nsmul a b x y)
    exact mem_stdMod.1 this 0
  · obtain ⟨g, hg, -, h2⟩ := h p hp
    obtain ⟨k, hk, hu⟩ := exists_uniform hp ((Lat.std E n).map g).fg h2
    refine ⟨k * k, fun hd => (hp.dvd_mul.1 hd).elim hk hk, ?_⟩
    rw [mul_smul]
    refine hu _ ⟨g.symm (k • x), (std_selfDual _).2 fun y hy => ?_, g.apply_symm_apply _⟩
    obtain ⟨o, ho⟩ := hx _ (hu _ ⟨y, hy, rfl⟩)
    refine ⟨o, ?_⟩
    rw [ho, ← hg (g.symm _), g.apply_symm_apply]
    have e1 := stdForm_nsmul 1 k x (g y)
    have e2 := stdForm_nsmul k 1 x (g y)
    rw [one_smul] at e1 e2
    rw [e2, mul_comm, ← e1]
    rfl

theorem exists_enum {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X) {n N : ℕ} {Λ : Lat E n}
    (hs : Λ.SelfDual) (h : Λ.Admissible l.M N) :
    ∃ e : Fin ((toGen Λ).zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G),
      Function.Injective e ∧ ∀ a, InZ Xo h a ↔ a ∈ Set.range e := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x β.hom hβ.symm
  have hN : 0 < N := h.1.pos
  have hN2 : 0 < N ^ 2 := pow_pos hN 2
  obtain ⟨zz, h1, h2, h3⟩ := ZCount.exists_class_representatives E H Dw n (toGen Λ) N ((unimod_iff Λ).2 hs) hN
    (((levOK_iff Λ N l.M).2 h).2.2.trans inf_le_left)
  let ev : Dw.La →+ Additive (ptO Xo x ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun v => Additive.ofMul (I.ev (N ^ 2) v)) fun a b => congrArg Additive.ofMul (I.add _ a b)
  have hsum : ∀ (cm : Fin n → 𝓞 E) (v : Fin n → Dw.La), I.ev (N ^ 2) (∑ j, cm j • v j) =
      (List.ofFn fun j => I.ev (N ^ 2) (v j) ≫ Xo.univ.t.act.act (cm j)).prod := fun cm v => by
    rw [List.prod_ofFn]
    refine (congrArg Additive.toMul (map_sum ev _ _)).trans ?_
    rw [toMul_sum]
    exact Finset.prod_congr rfl fun j _ => I.lin _ _ _
  have heq : ∀ u v, I.ev (N ^ 2) u = I.ev (N ^ 2) v ↔ Dw.ModN (N ^ 2) (u - v) := fun u v => by
    have e : I.ev (N ^ 2) u = I.ev (N ^ 2) (u - v) * I.ev (N ^ 2) v := by rw [← I.add, sub_add_cancel]
    rw [e, mul_eq_right, I.ker _ hN2]
    rfl
  refine ⟨fun i b => I.ev (N ^ 2) (zz i b), fun i j hij => h2 i j fun b => (heq _ _).1 (congrFun hij b),
    fun a => (inZh_iff Xo h a).symm.trans ⟨fun ha => ?_, ?_⟩⟩
  · choose v hv using fun b => (I.onto _ hN2 (a b)).1 (ha.1 b)
    obtain ⟨i, hi⟩ := h3 v fun mu hmu cm hcm i => (I.ker _ hN2 _).1 (by
      rw [hsum, ← ha.2 mu hmu cm hcm i]
      simp only [hv])
    exact ⟨i, funext fun b => ((heq _ _).2 (hi b)).symm.trans (hv b)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨fun b => (I.onto _ hN2 _).2 ⟨_, rfl⟩, fun mu hmu cm hcm j =>
      (hsum _ _).symm.trans ((I.ker _ hN2 _).2 (h1 i mu hmu cm hcm j))⟩

theorem inZ_comp {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T T' : Over Xo.X} (g : T' ⟶ T)
    {a : Fin n → (T ⟶ Xo.univ.t.G)} (ha : InZ Xo h a) : InZ Xo h fun b => g ≫ a b :=
  (inZh_iff Xo h _).1 (ZhStable.inZh_comp Xo _ N g a ((inZh_iff Xo h a).2 ha))

theorem geoInj_iff {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {n : ℕ} {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) :
    GeoInj Xo x0 z ↔ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : S →+* k),
      Function.Injective fun i b => ptRes Xo x0 ψ ≫ z i b := by
  refine ⟨fun h k _ _ ψ => h k ψ _ rfl, fun h k _ ψ g hg i j hij => ?_⟩
  refine h (AlgebraicClosure k) ((algebraMap k _).comp ψ) (funext fun b => Over.OverMorphism.ext ?_)
  have h1 : g.left ≫ (z i b).left = g.left ≫ (z j b).left := congrArg (fun f => f.left) (congrFun hij b)
  change spMap _ ≫ (z i b).left = spMap _ ≫ (z j b).left
  rw [hg] at h1
  rw [spMap_comp, Category.assoc, Category.assoc, h1]

theorem splitsZ_iff {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    {J : Type} (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) :
    SplitsZ Xo h x0 z ↔ (∀ i, InZh Xo (toGen Λ) N (z i)) ∧ GeoInj Xo x0 z ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : S →+* k) (a : Fin n → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)),
        InZh Xo (toGen Λ) N a → ∃ i, (fun b => ptRes Xo x0 ψ ≫ z i b) = a := by
  simp only [inZh_iff Xo h, geoInj_iff]
  refine and_congr_right fun hz => ⟨fun hs => ⟨fun k _ _ ψ i j hij => ?_, fun k _ _ ψ a ha => ?_⟩,
    fun ⟨h1, h2⟩ k _ _ ψ a ha => ?_⟩
  · exact (hs k ψ _ (inZ_comp Xo h _ (hz i))).unique (fun _ => rfl) (congrFun hij)
  · exact (hs k ψ a ha).exists.imp fun i hi => (funext hi).symm
  · obtain ⟨i, hi⟩ := h2 k ψ a ha
    exact ⟨i, fun b => (congrFun hi b).symm, fun j hj => h1 k ψ ((funext hj).symm.trans hi.symm)⟩

theorem splitsZ_iff_of_card {n N : ℕ} {Λ : Lat E n} (hs : Λ.SelfDual) (h : Λ.Admissible l.M N) {S : Type}
    [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (z : Fin ((toGen Λ).zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) :
    SplitsZ Xo h x0 z ↔ (∀ i, InZh Xo (toGen Λ) N (z i)) ∧ GeoInj Xo x0 z := by
  rw [splitsZ_iff]
  refine and_congr_right fun hz => and_iff_left_of_imp fun hg k _ _ ψ a ha => ?_
  obtain ⟨e, -, he⟩ := exists_enum Xo (spMap ψ ≫ x0) hs h
  choose τ hτ using fun i => (he _).1 (inZ_comp Xo h (ptRes Xo x0 ψ) ((inZh_iff Xo h _).1 (hz i)))
  have hi : Function.Injective τ := fun i j hij => hg k ψ (ptRes Xo x0 ψ) rfl
    ((hτ i).symm.trans ((congrArg e hij).trans (hτ j)))
  obtain ⟨j, rfl⟩ := (he a).1 ((inZh_iff Xo h a).1 ha)
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hi j
  exact ⟨i, (hτ i).symm⟩

theorem card_of_splitsZ {n N : ℕ} {Λ : Lat E n} (hs : Λ.SelfDual) (h : Λ.Admissible l.M N) {S : Type}
    [CommRing S] [Nontrivial S] {x0 : Sp S ⟶ Xo.X} {r : ℕ} {z : Fin r → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)}
    (hz : SplitsZ Xo h x0 z) : r = (toGen Λ).zCard N (Dw.p + Dw.q) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  let := Ideal.Quotient.field m
  let ψ : S →+* AlgebraicClosure (S ⧸ m) := (algebraMap (S ⧸ m) _).comp (Ideal.Quotient.mk m)
  obtain ⟨e, he1, he⟩ := exists_enum Xo (spMap ψ ≫ x0) hs h
  obtain ⟨h1, h2, h3⟩ := (splitsZ_iff Xo h x0 z).1 hz
  have hr : Set.range (fun i b => ptRes Xo x0 ψ ≫ z i b) = Set.range e := Set.ext fun a =>
    ⟨fun ⟨i, hi⟩ => (he a).1 (hi ▸ inZ_comp Xo h _ (hz.1 i)), fun ha => h3 _ ψ a ((inZh_iff Xo h a).2 ((he a).2 ha))⟩
  have := congrArg (fun s : Set _ => Nat.card s) hr
  rwa [Nat.card_range_of_injective (h2 _ ψ _ rfl), Nat.card_range_of_injective he1, Nat.card_fin, Nat.card_fin] at this

def normCoef {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) : (Fin n → NamedCl Dw l) → c.F :=
  fun q => (Nat.card (Fin n → LevQ Dw l) : c.F)⁻¹ * w q

theorem sum_eq {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (u : (Fin n → LevQ Dw l) → S) :
    algebraMap c.F S (β⁻¹ * (((toGen Λ).mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (w q) * u q =
    algebraMap c.F S (normFactor c Λ N β P) * ∑ t ∈ levelIndex Dw l n, algebraMap c.F S (normCoef c w t) * u t := by
  rw [finsum_eq_sum_of_support_subset _ (s := levelIndex Dw l n) (fun q _ => by simp [levelIndex]), mIdx_eq]
  simp only [normFactor, normCoef, map_mul, _root_.mul_assoc, ← Finset.mul_sum]
  ring

theorem shortValAt_iff_locVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {n N : ℕ} {Λ : Lat E n} (hs : Λ.SelfDual) (h : Λ.Admissible l.M N) (β : c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (v : S) :
    ShortValAt Xo c nab w (toGen Λ) β N P y v ↔ LocVal Xo c nab y h β (normCoef c w) P v := by
  have hN : N ≠ 0 := h.1.pos.ne'
  have hsq : ∀ {T : Over Xo.X} {t t' : T ⟶ Xo.univ.t.G}, t ^ N = 1 → t' ^ N = t → t' ^ (N ^ 2) = 1 :=
    fun h1 h2 => by rw [sq, pow_mul, h2, h1]
  constructor
  · rintro ⟨S', _, _, φ, y', z, tp, F, hφ, hy, hz, hg, ht, hF, hv⟩
    simp only [ShortDatumEq.levPt_levRep] at ht
    exact ⟨S', _, _, φ, y', hφ, hy, _, z, tp, F, (splitsZ_iff_of_card Xo hs h _ z).2 ⟨hz, hg⟩,
      fun q b => (isDivPt_iff Xo hN (levPtCl_pow Xo h.2.1 _ _) _).1 (ht q b),
      fun q i b => (isTwoLifts_iff _ _ _ _ _ _ _).2
        ⟨h.1, (hz i).1 b, hsq (levPtCl_pow Xo h.2.1 _ _) (ht q b).1, hF q i b⟩,
      hv.trans (sum_eq c Λ N β w P _)⟩
  · rintro ⟨S', _, _, φ, y', hφ, hy, r, z, tp, F, hz, ht, hF, hv⟩
    have ht' : ∀ q b, tp q b ^ N = levPt Xo y'.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b) :=
      fun q b => by
        rw [ShortDatumEq.levPt_levRep]
        exact (isDivPt_iff Xo hN (levPtCl_pow Xo h.2.1 _ _) _).2 (ht q b)
    rcases subsingleton_or_nontrivial S' with h0 | h0
    ·
      choose G hG using fun q b => ((exists_isVtOver_and_existsUnique_isUUOver abelianSchemeLaws_all.1 E H Dw l Xo N
        h.1 _ y'.s).2 1 (tp q b) (one_pow _) (hsq (levPtCl_pow Xo h.2.1 _ _) (ht q b).1)).exists
      exact ⟨S', _, _, φ, y', fun _ _ => 1, tp, fun q _ b => G q b, hφ, hy,
        fun _ => (inZh_iff Xo h _).2 (one_inZ Xo h), fun k _ ψ => (not_subsingleton k ψ.codomain_trivial).elim,
        ht', fun q _ b => hG q b, Subsingleton.elim _ _⟩
    · obtain rfl := card_of_splitsZ Xo hs h hz
      obtain ⟨h1, h2⟩ := (splitsZ_iff_of_card Xo hs h _ z).1 hz
      exact ⟨S', _, _, φ, y', z, tp, F, hφ, hy, h1, h2, ht',
        fun q i b => ((isTwoLifts_iff _ _ _ _ _ _ _).1 (hF q i b)).2.2.2, hv.trans (sum_eq c Λ N β w P _).symm⟩

theorem thVal_iff (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (Λ : Lat E n) (N : ℕ) (β : c.F) (w : (Fin n → LevQ Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) :
    ThVal Xo c nab y Λ N β (normCoef c w) a P v ↔
      (Λ.InGenus ∧ (toGen Λ).TrivAt l.M ∧ β ≠ 0 ∧ P ∈ harmL (Dw := Dw) c (toGen Λ) a) ∧ (toGen Λ).LevOK N l.M ∧
        ShortValAt Xo c nab w (toGen Λ) β N P y v := by
  rw [trivAt_iff, harmL_eq, levOK_iff]
  exact and_congr_right fun hr =>
    ⟨fun ⟨h, hv⟩ => ⟨h, (shortValAt_iff_locVal Xo c nab y (selfDual_of_inGenus hr.1) h β w P v).2 hv⟩,
      fun ⟨h, hv⟩ => ⟨h, (shortValAt_iff_locVal Xo c nab y (selfDual_of_inGenus hr.1) h β w P v).1 hv⟩⟩

theorem normCoef_x0Dat {n : ℕ} (x0 : Fin n → Dw.La) :
    normCoef c (x0Dat c x0) = fourier c (indicatorCl c (-ShortDatumEq.cls l x0)) :=
  funext fun q => ShortDatumEq.normalized_datum_eq_induced_coeff c x0 q

end GlobalTheory.ShortValueCompare
