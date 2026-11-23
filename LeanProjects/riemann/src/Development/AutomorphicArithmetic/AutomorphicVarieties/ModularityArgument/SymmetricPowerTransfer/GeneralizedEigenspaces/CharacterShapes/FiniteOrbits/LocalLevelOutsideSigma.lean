import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.SigMain
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ResCardAndUniformizer

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.LocalDataValidity

variable {F : Type} [Field F] [NumberField F]

private theorem mem_ov (v : Pl F) (x : Kv v) : x ∈ (v.adicCompletionIntegers F) ↔ valuation (Kv v) x ≤ 1 := by
  rw [← GroundTheory.Global.mem_valuationInteger_iff v x]
  exact Iff.rfl

private theorem isInts_v (v : Pl F) : IsInts (Kv v) (Ov v) :=
  ⟨Subtype.val_injective, fun x => ⟨by rintro ⟨y, rfl⟩; exact (mem_ov v _).1 y.2,
    fun h => ⟨⟨x, (mem_ov v x).2 h⟩, rfl⟩⟩⟩

private theorem two_v (v : Pl F) : (2 : Kv v) ≠ 0 := by
  intro h
  apply two_ne_zero (α := F)
  apply (cv v).injective
  rw [map_ofNat, map_zero]
  exact h

private theorem chi_unit (v : Pl F) {χ : (Kv v)ˣ →* ℂˣ} (h : Unr (Ov v) χ) : ∀ u ∈ Uo (Kv v), χ u = 1 := by
  intro u hu
  have hu1 : valuation (Kv v) (u : Kv v) = 1 := hu
  have h1 : (u : Kv v) ∈ v.adicCompletionIntegers F := (mem_ov v _).2 hu1.le
  have h2 : ((u⁻¹ : (Kv v)ˣ) : Kv v) ∈ v.adicCompletionIntegers F := (mem_ov v _).2 (by simp [hu1])
  let w : (Ov v)ˣ := ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have e : Units.map (algebraMap (Ov v) (Kv v) : Ov v →* Kv v) w = u := Units.ext rfl
  rw [← e]
  exact h w

private theorem hs_square {K : Type} [Field K] {D s : K} (h2 : (2 : K) ≠ 0) (h0 : s ≠ 0) (hss : s * s = D) (x : K) :
    Loc.hs D x = 1 := by
  unfold Loc.hs
  rw [if_pos]
  refine ⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩
  subst hss
  field_simp
  ring

private theorem chi_abs (v : Pl F) {D s : Kv v} (h0 : s ≠ 0) (hs : s * s = D) {χ : (Kv v)ˣ →* ℂˣ}
    (h : IsChi (Ov v) D χ) : χ = absPow (Kv v) 1 := by
  obtain ⟨hc, ϖ, ⟨p, hp, hpe⟩, hdec⟩ := GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F v
  have hS : (Valuation.integer (ValuativeRel.valuation (Kv v))) = (v.adicCompletionIntegers F).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff v x
  let e : 𝒪[Kv v] ≃+* Ov v := RingEquiv.subringCongr hS
  have hq : Irreducible (e p) := (MulEquiv.irreducible_iff e).2 hp
  have hcard : Nat.card (IsLocalRing.ResidueField (Ov v)) = GlobalTheory.SplitWeil.resCard (Kv v) := by
    rw [hc]
    exact GroundTheory.Global.natCard_residueField_adicCompletionIntegers (K := F) v
  have h1 : (χ ϖ : ℂ) = ((GlobalTheory.SplitWeil.resCard (Kv v) : ℕ) : ℂ)⁻¹ := by
    rw [h.2 (e p) ϖ hq hpe.symm, hs_square (two_v v) h0 hs, hcard, one_div]
  have h2 : ((absPow (Kv v) 1 ϖ : ℂˣ) : ℂ) = ((GlobalTheory.SplitWeil.resCard (Kv v) : ℕ) : ℂ)⁻¹ := by
    rw [val_absPow, Complex.cpow_one, GlobalTheory.SplitWeil.nabs_uniformiser hp hpe.symm]
    push_cast
    rfl
  have h3 : χ ϖ = absPow (Kv v) 1 ϖ := Units.ext (h1.trans h2.symm)
  ext t
  obtain ⟨a, u, hu1, hu2, rfl, -⟩ := hdec t
  have hv : valuation (Kv v) (u : Kv v) = 1 := by
    have a1 : valuation (Kv v) (u : Kv v) ≤ 1 := hu1
    have a2 : valuation (Kv v) ((u⁻¹ : (Kv v)ˣ) : Kv v) ≤ 1 := hu2
    refine le_antisymm a1 ?_
    have a3 : valuation (Kv v) (u : Kv v) * valuation (Kv v) ((u⁻¹ : (Kv v)ˣ) : Kv v) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : _) = valuation (Kv v) (u : Kv v) * valuation (Kv v) ((u⁻¹ : (Kv v)ˣ) : Kv v) := a3.symm
      _ ≤ valuation (Kv v) (u : Kv v) * 1 := by gcongr
      _ = _ := mul_one _
  have hx : absPow (Kv v) 1 u = 1 := by
    apply Units.ext
    rw [val_absPow, (GlobalTheory.SplitWeil.nabs_eq_one_iff u).2 hv]
    simp
  rw [map_mul, map_mul, chi_unit v h.1 u (show u ∈ Uo (Kv v) from hv), hx, map_zpow, map_zpow, h3]

private theorem exists_real (h : IsTotallyReal F) : Nonempty (F →+* ℝ) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  exact ⟨InfinitePlace.embedding_of_isReal (h.isReal (InfinitePlace.mk φ))⟩

variable {Δ : F}

private theorem s_ne (A : SD Δ) (hA : A.Ok) (v : Pl F) (h : v ∈ A.Sg) : A.s v ≠ 0 := by
  intro h0
  obtain ⟨σ⟩ := exists_real hA.real
  have h1 : cv v Δ = 0 := by rw [← A.hs v h, h0, mul_zero]
  have h2 : Δ = 0 := (map_eq_zero _).1 h1
  have h3 := hA.neg σ
  rw [h2, map_zero] at h3
  exact lt_irrefl _ h3

private theorem dat_S (A : SD Δ) (v : Pl F) (h : v ∈ A.Sg) :
    A.dat.S v = (A.V v).data (A.hs v h) (A.Ry v) (A.χ v) := dif_pos h

private theorem dat_Jv (A : SD Δ) (v : Pl F) (h : v ∈ A.Sg) :
    A.dat.Jv v = ((A.V v).J 3).comap (eU (A.hs v h)) := by
  have e : A.dat.Jv v = (A.dat.S v).J := if_pos h
  rw [e, dat_S A v h]
  rfl

private theorem dat_Jv' (A : SD Δ) (v : Pl F) (h : v ∉ A.Sg) : A.dat.Jv v = KU (Ov v) _ := if_neg h

private theorem local_level_at_sigma (A : SD Δ) (v : Pl F) (h : v ∈ A.Sg) :
    A.dat.J2v v = ((A.V v).J 2).comap (eD (A.hs v h)) := by
  have e : A.dat.J2v v = (A.dat.S v).J2 := if_pos h
  rw [e, dat_S A v h]
  rfl

private theorem local_level_outside_sigma (A : SD Δ) (v : Pl F) (h : v ∉ A.Sg) : A.dat.J2v v = KD _ (Ov v) := if_neg h

private theorem mem_UG (A : SD Δ) (g : GA Δ) : g ∈ A.dat.UG ↔ ∀ v, g.1 v ∈ A.dat.Jv v := by
  unfold Dat.UG RPG.box
  rw [Subgroup.mem_iInf]
  exact Iff.rfl

private theorem mem_level_two_iff_local (A : SD Δ) (g : DA Δ) : g ∈ A.dat.U2 ↔ ∀ v, g.1 v ∈ A.dat.J2v v := by
  unfold Dat.U2 RPG.box
  rw [Subgroup.mem_iInf]
  exact Iff.rfl

end UpperTheory.V.Z.Sym.So.LocalDataValidity

open UpperTheory.V.Z.Sym.So.LocalDataValidity in
theorem UpperTheory.V.Z.Sym.So.datOk :
    UpperTheory.V.Z.Sym.So.DatOk := by
  intro F _ _ Δ A hA
  have hchi : ∀ v, ∀ u ∈ Uo (Kv v), A.χ v u = 1 := fun v => chi_unit v (hA.chi v).1
  refine ⟨⟨hA.real, hA.neg, hA.ne, hA.off, fun v h => ⟨A.s v, (A.hs v h).symm⟩, hA.chi, fun v h => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [dat_S A v h]
    exact sigMain (Kv v) (Ov v) (isInts_v v) (two_v v) _ _ (A.hs v h) (s_ne A hA v h) _ _ (hA.ry v h) _ (hchi v)
  · intro t
    refine forall₂_congr fun v h => ?_
    rw [dat_S A v h]
    exact Iff.rfl
  · intro v h
    exact ⟨isInts_v v, two_v v, s_ne A hA v h, hchi v, chi_abs v (s_ne A hA v h) (A.hs v h) (hA.chi v)⟩
  · intro g
    rw [mem_UG]
    constructor
    · intro H
      refine ⟨fun v h => ?_, fun v h => ?_⟩
      · have := H v
        rw [dat_Jv A v h] at this
        exact this
      · have := H v
        rwa [dat_Jv' A v h] at this
    · rintro ⟨H1, H2⟩ v
      by_cases h : v ∈ A.Sg
      · rw [dat_Jv A v h]
        exact H1 v h
      · rw [dat_Jv' A v h]
        exact H2 v h
  · intro g
    rw [mem_level_two_iff_local]
    constructor
    · intro H
      refine ⟨fun v h => ?_, fun v h => ?_⟩
      · have := H v
        rw [local_level_at_sigma A v h] at this
        exact this
      · have := H v
        rwa [local_level_outside_sigma A v h] at this
    · rintro ⟨H1, H2⟩ v
      by_cases h : v ∈ A.Sg
      · rw [local_level_at_sigma A v h]
        exact H1 v h
      · rw [local_level_outside_sigma A v h]
        exact H2 v h

end
