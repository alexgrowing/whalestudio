import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.UfDg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RestrictedProductBoxFibre
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.DiagDC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.KO

private theorem coset_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (U W : Subgroup G) (hUW : U ≤ W) (ω : W →* ℂˣ) (f : G → ℂ) (a : G) (c : ℂ) (hc : c ≠ 0)
    (hf : ∀ (u : W) y, f (y * u) = ((ω u)⁻¹ : ℂˣ) * f y)
    (φ : G → V) (hφ : ∀ g (u : W), φ (g * u) = (ω u : ℂ) • φ g)
    (hval : ∀ y ∈ DC U a, f y = c)
    (hsupp : ∀ y, f y ≠ 0 → ∃ u ∈ W, y * u ∈ DC U a)
    (huniq : ∀ y ∈ DC U a, ∀ u ∈ W, y * u ∈ DC U a → u ∈ U) (h : G) :
    ∑ᶠ x : G ⧸ W, f x.out • φ (h * x.out) = c • ∑ᶠ (y : G ⧸ U) (_ : y.out ∈ DC U a), φ (h * y.out) := by
  have hinv : ∀ (y : G) (u : W), f (y * u) • φ (h * (y * u)) = f y • φ (h * y) := by
    intro y u
    rw [hf, ← mul_assoc, hφ, smul_smul, Units.val_inv_eq_inv_val]
    congr 1
    have := Units.ne_zero (ω u)
    field_simp
  have hne : ∀ (y : G) (u : W), f y ≠ 0 → f (y * u) ≠ 0 := fun y u hy => by
    rw [hf]
    exact mul_ne_zero (Units.ne_zero _) hy
  have hDC : ∀ y ∈ DC U a, ∀ w ∈ U, y * w ∈ DC U a := by
    rintro _ ⟨p, hp, q, hq, rfl⟩ w hw
    exact ⟨p, hp, q * w, mul_mem hq hw, by simp [mul_assoc]⟩
  have hout : ∀ y : G ⧸ U, y.out ∈ DC U a → f ((y.out : G ⧸ W)).out ≠ 0 := fun y hy => by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul W y.out
    rw [hu]
    exact hne _ _ (by rw [hval _ hy]; exact hc)
  have hb : Set.BijOn (fun y : G ⧸ U => (y.out : G ⧸ W)) {y | y.out ∈ DC U a} {x | f x.out ≠ 0} := by
    refine ⟨fun y hy => hout y hy, fun y hy y' hy' e => ?_, fun x hx => ?_⟩
    · have e' : y.out⁻¹ * y'.out ∈ W := QuotientGroup.eq.1 e
      have := huniq _ hy _ e' (by simpa using hy')
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      exact QuotientGroup.eq.2 this
    · obtain ⟨u, hu, hxu⟩ := hsupp _ hx
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul U (x.out * u)
      refine ⟨((x.out * u : G) : G ⧸ U), ?_, ?_⟩
      · change Quotient.out _ ∈ DC U a
        rw [hw]
        exact hDC _ hxu _ w.2
      · change ((Quotient.out ((x.out * u : G) : G ⧸ U) : G) : G ⧸ W) = x
        rw [hw, ← QuotientGroup.out_eq' x, QuotientGroup.eq]
        simpa [mul_assoc] using inv_mem (mul_mem hu (hUW w.2))
  have h1 : ∑ᶠ x : G ⧸ W, f x.out • φ (h * x.out) = ∑ᶠ x ∈ {x : G ⧸ W | f x.out ≠ 0}, f x.out • φ (h * x.out) := by
    refine finsum_congr fun x => ?_
    rw [finsum_eq_if]
    split_ifs with hx
    · rfl
    · have : f x.out = 0 := by simpa using hx
      rw [this, zero_smul]
  have h2 : c • ∑ᶠ (y : G ⧸ U) (_ : y.out ∈ DC U a), φ (h * y.out) =
      ∑ᶠ y ∈ {y : G ⧸ U | y.out ∈ DC U a}, c • φ (h * y.out) := by
    rw [smul_finsum]
    refine finsum_congr fun y => ?_
    rw [smul_finsum]
    rfl
  rw [h1, h2]
  symm
  refine finsum_mem_eq_of_bijOn _ hb fun y hy => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul W y.out
  change c • φ (h * y.out) = f (Quotient.out ((y.out : G) : G ⧸ W)) • φ (h * Quotient.out ((y.out : G) : G ⧸ W))
  rw [hu, hinv, hval _ hy]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem scalar_eq (n : ℕ) (z : kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) z : GL (Fin n) k) = dg (fun _ => z) := by
  apply Units.ext
  rw [val_diagT]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.scalar_apply]

private theorem gl_uniq (V : Lev k) (d : Fin 2 → kˣ) (hd : Dom d) {Y u : GL (Fin 2) k} (hY : Y ∈ V.DC d) (hYu : Y * u ∈ V.DC d)
    (z : kˣ) (j : GL (Fin 2) k) (hj : j ∈ V.J 2) (hu : u = Matrix.GeneralLinearGroup.scalar (Fin 2) z * j) : u ∈ V.J 2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hY
  obtain ⟨p, hp, q, hq, e⟩ := hYu
  have hcomm : ∀ g : GL (Fin 2) k, g * dg (fun _ => z) = dg (fun _ => z) * g := fun g => by
    rw [← scalar_eq]
    apply Units.ext
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq.symm
  have h1 : dg (d * fun _ => z) ∈ V.DC d := by
    refine ⟨a⁻¹ * p, mul_mem (inv_mem ha) hp, q * j⁻¹ * b⁻¹, mul_mem (mul_mem hq (inv_mem hj)) (inv_mem hb), ?_⟩
    have : dg (d * fun _ => z) = a⁻¹ * (a * dg d * b * u) * j⁻¹ * b⁻¹ := by
      rw [hu, scalar_eq]
      simp only [dg, map_mul]
      have := hcomm b
      simp only [dg] at this
      rw [show a⁻¹ * (a * diagT k (Fin 2) d * b * ((diagT k (Fin 2) fun _ => z) * j)) * j⁻¹ * b⁻¹ = diagT k (Fin 2) d * (b * (diagT k (Fin 2) fun _ => z)) * b⁻¹ by group, this]
      group
    rw [this, e]
    group
  have h2 := (diagDC k V 2 d _ hd).1 h1 0
  have h3 : z ∈ V.H := by simpa using h2
  rw [hu, scalar_eq]
  refine mul_mem ?_ hj
  exact le_sup_left (b := (glIwa k 2).Nm V.c) (le_sup_right (a := (glIwa k 2).N) ⟨fun _ => z, fun i _ => h3, rfl⟩)

end Loc

section Loc2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem val_lt (t : kˣ) (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2) : valuation k (t : k) < 1 := by
  have hex : ∃ x : kˣ, valuation k (x : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact uniformizer_ne_zero hx.symm
    exact ⟨Units.mk0 x h0, hx⟩
  have hu : valuation k (unif k : k) = uniformizer k := Classical.epsilon_spec hex
  have h1 : valuation k (unif k : k) ≤ 1 := by
    rw [hu]; exact uniformizer_lt_one.le
  exact lt_of_lt_of_le ht (pow_le_one' h1 2)

private theorem sdom {t : kˣ} (ht : valuation k (t : k) < 1) : SDom (![t, 1] : Fin 2 → kˣ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem dom_of {t : kˣ} (ht : valuation k (t : k) < 1) : Dom (![t, 1] : Fin 2 → kˣ) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (sdom ht i j h).le

private theorem kirillov_function_value_eq (V : Lev k) (χ : kˣ →* ℂˣ) (hχ : ∀ u ∈ V.H, χ u = 1) {t : kˣ} (ht : valuation k (t : k) < 1)
    {Y : GL (Fin 2) k} (hY : Y ∈ V.DC ![t, 1]) : V.twistedCentralTestFunction χ t Y = (((χ t)⁻¹ : ℂˣ) : ℂ) := by
  obtain ⟨-, -, hz⟩ := eqZ k V χ hχ 2 (by norm_num)
  have h := (hz _ (sdom ht)).1 1 Y hY
  rw [map_one, one_mul, map_one, inv_one, Units.val_one] at h
  rw [Lev.twistedCentralTestFunction, h, mul_one]

private theorem kirillov_function_support (V : Lev k) (χ : kˣ →* ℂˣ) {t : kˣ} {Y : GL (Fin 2) k} (hY : V.twistedCentralTestFunction χ t Y ≠ 0) :
    ∃ z : kˣ, (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * Y ∈ V.DC ![t, 1] := by
  by_contra h
  apply hY
  rw [Lev.twistedCentralTestFunction, Lev.fZ, dif_neg h, mul_zero]

end Loc2

section Glb

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

private theorem scal_one' {K : Type} [Field K] {Δ : K} : IsScal (1 : Kˣ) (1 : DX Δ) := by
  simp [IsScal, mt]

private theorem scal_comm' {K : Type} [Field K] {Δ : K} {z : Kˣ} {s : DX Δ} (h : IsScal z s) (y : DX Δ) : s * y = y * s := by
  apply Subtype.ext
  apply Units.ext
  change mt s * mt y = mt y * mt s
  rw [h]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

private theorem dat_S (v : Pl F) (h : v ∈ A.Sg) : A.dat.S v = (A.V v).data (A.hs v h) (A.Ry v) (A.χ v) := dif_pos h

private theorem level_two_at_sigma (v : Pl F) (h : v ∈ A.Sg) : A.dat.J2v v = ((A.V v).J 2).comap (eD (A.hs v h)) := by
  have h' : v ∈ A.dat.Sg := h
  rw [Dat.J2v, if_pos h', dat_S A v h]
  rfl

private theorem level_two_outside_sigma (v : Pl F) (h : v ∉ A.Sg) : A.dat.J2v v = KD _ (Ov v) := if_neg h

private theorem fK_sig (t : Dat.Par F) (v : Pl F) (h : v ∈ A.Sg) (x : DX (cv v Δ)) :
    A.dat.fKv t v x = (A.V v).twistedCentralTestFunction (A.χ v) (t v) (eD (A.hs v h) x) := by
  have h' : v ∈ A.dat.Sg := h
  rw [Dat.fKv, if_pos h', dat_S A v h]
  rfl

private theorem fK_off (t : Dat.Par F) (v : Pl F) (h : v ∉ A.Sg) (x : DX (cv v Δ)) :
    A.dat.fKv t v x = fZD (Ov v) (A.χ v) x := if_neg h

variable {A}

private theorem bij_sig (hA : A.Ok) (v : Pl F) (h : v ∈ A.Sg) : Function.Bijective (eD (A.hs v h)) := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  obtain ⟨h1, h2, h3, -⟩ := hl v h
  exact (eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v h) h3).1

private theorem dc_sig (hA : A.Ok) {g : DA Δ} {d : ParN F 2} (hg : A.IsElD g d) (v : Pl F) (h : v ∈ A.Sg) (y : DX (cv v Δ)) :
    y ∈ DC (A.dat.J2v v) (g.1 v) ↔ eD (A.hs v h) y ∈ (A.V v).DC (d v) := by
  rw [level_two_at_sigma A v h]
  constructor
  · rintro ⟨u, hu, u', hu', rfl⟩
    exact ⟨_, hu, _, hu', by rw [map_mul, map_mul, hg.1 v h]⟩
  · rintro ⟨a, ha, b, hb, e⟩
    obtain ⟨u, rfl⟩ := (bij_sig hA v h).2 a
    obtain ⟨u', rfl⟩ := (bij_sig hA v h).2 b
    exact ⟨u, ha, u', hb, (bij_sig hA v h).1 (by rw [e, map_mul, map_mul, hg.1 v h])⟩

private theorem dc_box (hA : A.Ok) {g : DA Δ} {d : ParN F 2} (hg : A.IsElD g d) (y : DA Δ) :
    y ∈ DC A.dat.U2 g ↔ (∀ v (h : v ∈ A.Sg), eD (A.hs v h) (y.1 v) ∈ (A.V v).DC (d v)) ∧ ∀ v ∉ A.Sg, y.1 v ∈ KD _ (Ov v) := by
  have h := (uFBox (Pl F) (DA Δ) (fun v => DX (cv v Δ)) (fun v => KD (cv v Δ) (Ov v)) A.dat.J2v (rpg _ _) A.Sg
    (fun v hv => level_two_outside_sigma A v hv) g (fun v hv => by
      change g.1 v ∈ _
      rw [hg.2 v hv]
      exact one_mem _)).1 y
  refine h.trans ⟨fun ⟨a, b⟩ => ⟨fun v hv => (dc_sig hA hg v hv _).1 (a v hv), fun v hv => ?_⟩,
    fun ⟨a, b⟩ => ⟨fun v hv => (dc_sig hA hg v hv _).2 (a v hv), fun v hv => ?_⟩⟩
  · have := b v hv
    rwa [level_two_outside_sigma A v hv] at this
  · rw [level_two_outside_sigma A v hv]
    exact b v hv

private theorem fk_one (hA : A.Ok) (t : Dat.Par F) (v : Pl F) (hv : v ∉ A.Sg) (x : DX (cv v Δ)) (hx : x ∈ KD _ (Ov v)) :
    A.dat.fKv t v x = 1 := by
  have := (Loc.fzdLaw (Ov v) (Kv v) (cv v Δ) (hA.off v hv) (A.χ v) (hA.chi v).1).2 1 1 x scal_one' hx
  rw [one_mul, map_one, inv_one, Units.val_one] at this
  rw [fK_off A t v hv, this]

private theorem fk_val (hA : A.Ok) {t : Dat.Par F} (ht : A.Cone t) {g : DA Δ} (hg : A.IsElD g fun v => ![t v, 1]) (y : DA Δ)
    (hy : y ∈ DC A.dat.U2 g) : A.dat.FK t y = ∏ v ∈ A.Sg, (((A.χ v (t v))⁻¹ : ℂˣ) : ℂ) := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  obtain ⟨a, b⟩ := (dc_box hA hg y).1 hy
  rw [Dat.FK, finprod_eq_prod_of_mulSupport_subset (s := A.Sg)]
  · refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨-, -, -, h4, -⟩ := hl v hv
    rw [fK_sig A t v hv]
    exact kirillov_function_value_eq _ _ (fun u hu => h4 u ((A.V v).H_le hu)) (val_lt _ (ht v hv)) (a v hv)
  · intro v hv
    by_contra h
    exact hv (fk_one hA t v h _ (b v h))

private theorem fk_supp (hA : A.Ok) {t : Dat.Par F} {g : DA Δ} (hg : A.IsElD g fun v => ![t v, 1]) (y : DA Δ)
    (hy : A.dat.FK t y ≠ 0) : ∃ u ∈ A.dat.UZ, y * u ∈ DC A.dat.U2 g := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  have hco : ∀ᶠ v in Filter.cofinite, v ∉ A.Sg := Filter.eventually_cofinite.2 (by simpa using A.Sg.finite_toSet)
  have hyK : ∀ᶠ v in Filter.cofinite, y.1 v ∈ KD (cv v Δ) (Ov v) := (rpg _ _).ae y
  have hfin : (Function.mulSupport fun v => A.dat.fKv t v (y.1 v)).Finite := by
    refine (Filter.eventually_cofinite.1 (hco.and hyK)).subset fun v hv h => hv ?_
    exact fk_one hA t v h.1 _ h.2
  have hne : ∀ v, A.dat.fKv t v (y.1 v) ≠ 0 := fun v h => hy (finprod_eq_zero _ v h hfin)
  have hloc : ∀ v, ∃ (z : (Kv v)ˣ) (s : DX (cv v Δ)), IsScal z s ∧
      (∀ h : v ∈ A.Sg, eD (A.hs v h) (s⁻¹ * y.1 v) ∈ (A.V v).DC ![t v, 1]) ∧ (v ∉ A.Sg → s⁻¹ * y.1 v ∈ KD _ (Ov v)) := by
    intro v
    by_cases hv : v ∈ A.Sg
    · have h0 := hne v
      rw [fK_sig A t v hv] at h0
      obtain ⟨z, hz⟩ := kirillov_function_support _ _ h0
      obtain ⟨h1, h2, h3, -⟩ := hl v hv
      obtain ⟨hb, -, -, hscal, -⟩ := eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v hv) h3
      obtain ⟨s, hs⟩ := hb.2 (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
      exact ⟨z, s, (hscal z s).2 hs, fun _ => by rwa [map_mul, map_inv, hs], fun h => (h hv).elim⟩
    · have h0 := hne v
      rw [fK_off A t v hv] at h0
      have : ∃ (z : (Kv v)ˣ) (s : DX (cv v Δ)), IsScal z s ∧ s⁻¹ * y.1 v ∈ KD _ (Ov v) := by
        by_contra hh
        exact h0 (dif_neg hh)
      obtain ⟨z, s, hs, hk⟩ := this
      exact ⟨z, s, hs, fun h => (hv h).elim, fun _ => hk⟩
  choose z s hs hS hO using hloc
  have hmem : ∀ᶠ v in Filter.cofinite, (s v)⁻¹ ∈ KD (cv v Δ) (Ov v) :=
    (hco.and hyK).mono fun v h => by simpa using mul_mem (hO v h.1) (inv_mem h.2)
  refine ⟨⟨fun v => (s v)⁻¹, hmem⟩, Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 (Subgroup.mem_sup_left (inv_mem ⟨z v, Units.ext (hs v).symm⟩)), ?_⟩
  have hc : ∀ v, (y * ⟨fun v => (s v)⁻¹, hmem⟩ : DA Δ).1 v = (s v)⁻¹ * y.1 v := fun v => by
    change y.1 v * (s v)⁻¹ = _
    have := scal_comm' (hs v) (y.1 v)
    rw [eq_comm, inv_mul_eq_iff_eq_mul, ← mul_assoc, this, mul_inv_cancel_right]
  refine (dc_box hA hg _).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [hc]
    exact hS v hv
  · rw [hc]
    exact hO v hv

private theorem fk_uniq (hA : A.Ok) {t : Dat.Par F} (ht : A.Cone t) {g : DA Δ} (hg : A.IsElD g fun v => ![t v, 1]) (y : DA Δ)
    (hy : y ∈ DC A.dat.U2 g) (u : DA Δ) (hu : u ∈ A.dat.UZ) (hyu : y * u ∈ DC A.dat.U2 g) : u ∈ A.dat.U2 := by
  obtain ⟨-, -, hl, -⟩ := datOk F Δ A hA
  obtain ⟨a, a'⟩ := (dc_box hA hg y).1 hy
  obtain ⟨b, b'⟩ := (dc_box hA hg _).1 hyu
  refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
  have huv : u.1 v ∈ ZD _ ⊔ A.dat.J2v v := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu v)
  change u.1 v ∈ A.dat.J2v v
  by_cases hv : v ∈ A.Sg
  · rw [level_two_at_sigma A v hv] at huv ⊢
    obtain ⟨h1, h2, h3, h4, -⟩ := hl v hv
    obtain ⟨-, -, -, -, -, hZJ⟩ := eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v hv) h3
    rw [← hZJ] at huv
    obtain ⟨-, hm, -⟩ := eqZ _ (A.V v) (A.χ v) (fun u hu => h4 u ((A.V v).H_le hu)) 2 (by norm_num)
    obtain ⟨z, j, hj, e⟩ := (hm _).1 huv
    have hb := b v hv
    have hbb : eD (A.hs v hv) (y.1 v) * eD (A.hs v hv) (u.1 v) ∈ (A.V v).DC ![t v, 1] := by
      rw [← map_mul]
      exact hb
    exact gl_uniq _ _ (dom_of (val_lt _ (ht v hv))) (a v hv) hbb z j hj e
  · rw [level_two_outside_sigma A v hv]
    exact (mul_mem_cancel_left (a' v hv)).1 (b' v hv)

end Glb

end UpperTheory.V.Z.Sym.So.KO

open UpperTheory.V.Z.Sym.So.KO in
theorem UpperTheory.V.Z.Sym.So.kOps :
    UpperTheory.V.Z.Sym.So.KOps := by
  intro F _ _ Δ A hA V _ _ ch B hB
  obtain ⟨hOk, hCone, hl, -, -⟩ := datOk F Δ A hA
  have hle : A.dat.U2 ≤ B.U := fun u hu => by
    rw [hB.U]
    exact Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_iInf.1 hu v))
  have hinv : ∀ φ ∈ B.Forms, ∀ u ∈ A.dat.U2, ∀ g, φ (g * u) = φ g := by
    intro φ hφ u hu g
    have h1 := hφ.2 g ⟨u, hle hu⟩
    have h2 := hB.ω ⟨u, hle hu⟩ (fun _ => 1) (fun _ => 1) fun v =>
      ⟨scal_one', by
        have h0 : u.1 v ∈ A.dat.J2v v := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu v)
        simpa using h0⟩
    simp only [map_one, Units.val_one, finprod_one] at h2
    rw [h2, one_smul] at h1
    exact h1
  refine ⟨fun t g ht hg φ => ?_, hinv, fun φ hφ z s hs g => ?_⟩
  · have ht' : A.dat.Cone t := (hCone t).2 ht
    have htest := finK_test F Δ A.dat hOk V ch B hB t ht'
    rw [Tf.rSpec _ _ _ B (Base.Tw.one B) _ htest φ]
    funext h
    have hdc := (dcBasic (DA Δ) V A.dat.U2 g (dMul F Δ A hA g _ hg).1 φ.1 (hinv φ.1 φ.2)).2.1 h
    rw [Pi.smul_apply, hdc]
    refine coset_sum A.dat.U2 B.U hle B.ω (A.dat.FK t) g _ (Finset.prod_ne_zero_iff.2 fun v _ => Units.ne_zero _)
      (fun u y => htest.right u y) φ.1 (fun g u => φ.2.2 g u) (fk_val hA ht hg) (fun y hy => ?_) (fun y hy u hu hyu => ?_) h
    · obtain ⟨u, hu, e⟩ := fk_supp hA hg y hy
      exact ⟨u, hB.U ▸ hu, e⟩
    · exact fk_uniq hA ht hg y hy u (hB.U ▸ hu) hyu
  · classical
    let z' : Dat.Par F := fun v => if v ∈ A.Sg then z v else 1
    have hsc : ∀ v, IsScal (z' v) (s.1 v) := fun v => by
      by_cases hv : v ∈ A.Sg
      · obtain ⟨h1, h2, h3, -⟩ := hl v hv
        obtain ⟨-, -, -, hscal, -⟩ := eD_facts (Kv v) (Ov v) h1 h2 _ _ (A.hs v hv) h3
        have hz : z' v = z v := if_pos hv
        rw [hz, hscal, hs.1 v hv, scalar_eq]
        congr 1
        funext i
        fin_cases i <;> rfl
      · have hz : z' v = 1 := if_neg hv
        rw [hz, hs.2 v hv]
        exact scal_one'
    have hsU : s ∈ B.U := by
      rw [hB.U]
      exact Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨z' v, Units.ext (hsc v).symm⟩)
    have h1 := hφ.2 g ⟨s, hsU⟩
    have h2 := hB.ω ⟨s, hsU⟩ z' (fun v => s.1 v) fun v => ⟨hsc v, by simp⟩
    have h3 : (∏ᶠ v, (A.dat.χ v (z' v) : ℂ)) = ∏ v ∈ A.Sg, (A.χ v (z v) : ℂ) := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := A.Sg)]
      · refine Finset.prod_congr rfl fun v hv => ?_
        have hz : z' v = z v := if_pos hv
        rw [hz]
        rfl
      · intro v hv
        by_contra h
        have hz : z' v = 1 := if_neg h
        exact hv (by
          change ((A.dat.χ v (z' v) : ℂˣ) : ℂ) = 1
          rw [hz]
          simp)
    rw [h2, h3] at h1
    exact h1

end
