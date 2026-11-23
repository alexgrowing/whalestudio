import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.KirillovFunctionValueEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.UfDg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.TorPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem dc_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (S U : Subgroup G) (hS : S.Normal) (a : S) (y : G)
    (hy : y * (a : G) = a * y) (hfin : AlgebraTools.FinOrb U U (a : G))
    (hc : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (φ : G → V) (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g) (g : S) :
    dcF ((U.comap (MulAut.conj y⁻¹).toMonoidHom).subgroupOf S) a (fun h : S => φ (h * y)) g = dcF U (a : G) φ (g * y) := by
  classical
  have hmem : ∀ u : G, u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom ↔ y⁻¹ * u * y ∈ U := by
    intro u
    simp [MulAut.conj_apply]
  have hea : (MulAut.conj y⁻¹).toMonoidHom (a : G) = a := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← hy, inv_mul_cancel_left]
  have hbij : Function.Bijective (MulAut.conj y⁻¹).toMonoidHom := (MulAut.conj y⁻¹).bijective
  have hM := dcMap G G V (MulAut.conj y⁻¹).toMonoidHom hbij U (a : G) (a : G)
  rw [hea] at hM
  obtain ⟨-, hfinIff, -, hmap⟩ := hM
  have hfin' := hfinIff.2 hfin
  have hφy : ∀ u ∈ U, ∀ x : G, φ (y * (x * u)) = φ (y * x) := by
    intro u hu x
    rw [← mul_assoc]
    exact hφ u hu _
  have htr : ∀ z : G, dcF U (a : G) (fun x => φ (y * x)) z = dcF U (a : G) φ (y * z) := by
    intro z
    rw [(dcBasic G V U a hfin (fun x => φ (y * x)) hφy).2.1, (dcBasic G V U a hfin φ hφ).2.1]
    simp only [mul_assoc]
  have hA : ∀ x : G, dcF (U.comap (MulAut.conj y⁻¹).toMonoidHom) (a : G) (fun h => φ (h * y)) x
      = dcF U (a : G) φ (x * y) := by
    intro x
    have h1 := congrFun (hmap hfin (fun x => φ (y * x)) hφy) x
    have h2 : ((fun x => φ (y * x)) ∘ (MulAut.conj y⁻¹).toMonoidHom) = fun h => φ (h * y) := by
      funext h
      simp [MulAut.conj_apply, mul_assoc]
    rw [h2] at h1
    rw [h1]
    simp only [Function.comp_apply]
    rw [htr]
    simp [MulAut.conj_apply, mul_assoc]
  have hay : (a : G) * y⁻¹ = y⁻¹ * a := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hy, inv_mul_cancel_left]
  have hc' : ∀ u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom, ∃ c ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom,
      c * (a : G) = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S := by
    intro u hu
    obtain ⟨c, hcU, hca, h1, h2⟩ := hc _ ((hmem u).1 hu)
    refine ⟨y * c * y⁻¹, (hmem _).2 (by simpa [mul_assoc] using hcU), ?_, ?_, ?_⟩
    · calc y * c * y⁻¹ * (a : G) = y * c * (a * y⁻¹) := by rw [hay, mul_assoc]
        _ = y * (c * a) * y⁻¹ := by simp only [mul_assoc]
        _ = y * a * c * y⁻¹ := by rw [hca]; simp only [mul_assoc]
        _ = (a : G) * (y * c * y⁻¹) := by rw [hy]; simp only [mul_assoc]
    · have := hS.conj_mem _ h1 y
      simpa [mul_assoc] using this
    · have := hS.conj_mem _ h2 y
      simpa [mul_assoc] using this
  have hψG : ∀ u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom, ∀ x : G, φ (x * u * y) = φ (x * y) := by
    intro u hu x
    have := hφ _ ((hmem u).1 hu) (x * y)
    simpa [mul_assoc] using this
  obtain ⟨hfS, hDC, -, R, hR1, hR2, hR3⟩ := dcSub G V S _ a hfin' hc' hS
  have hψS : ∀ u ∈ (U.comap (MulAut.conj y⁻¹).toMonoidHom).subgroupOf S, ∀ x : S,
      φ (((x * u : S) : G) * y) = φ ((x : G) * y) := by
    intro u hu x
    rw [Subgroup.mem_subgroupOf] at hu
    simpa using hψG _ hu x
  rw [(dcBasic S V _ a hfS (fun h : S => φ (h * y)) hψS).2.2.2.2 R hR1 hR2 g, ← hA]
  rw [(dcBasic G V _ (a : G) hfin' (fun h => φ (h * y)) hψG).2.2.2.2 (R.map (Function.Embedding.subtype _)) ?_ ?_ g]
  · rw [Finset.sum_map]
    simp
  · intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hz
    exact (hDC r).1 (hR1 r hr)
  · intro z hz
    obtain ⟨r, ⟨hr, hrz⟩, huniq⟩ := hR3 z hz
    refine ⟨(r : G), ⟨Finset.mem_map_of_mem _ hr, hrz⟩, ?_⟩
    rintro w ⟨hw, hwz⟩
    obtain ⟨r', hr', rfl⟩ := Finset.mem_map.1 hw
    exact congrArg Subtype.val (huniq r' ⟨hr', hwz⟩)

private theorem sa_normal {F : Type} [Field F] [NumberField F] (Δ : F) : (SA Δ).Normal := by
  unfold SA
  refine Subgroup.normal_iInf_normal fun v => ?_
  have hN : (SU ((cv v) Δ)).Normal := by
    unfold SU
    exact MonoidHom.normal_ker _
  exact hN.comap _

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.kRes :
    UpperTheory.V.Z.Sym.So.KRes := by
  intro F _ _ Δ A hA V _ _ ch C hC y hy φ hφ a ha
  have hK := kOps F Δ A hA V ch C hC
  have hφU : ∀ u ∈ A.dat.U2, ∀ g : DA Δ, φ (g * u) = φ g := hK.2.1 φ hφ
  constructor
  · intro γ g g' hg
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [hg, mul_assoc]
    exact hφ.1 (γ : DX Δ) _
  · intro u hu g
    unfold SD.lvS at hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hu
    have := hφU _ hu ((g : DA Δ) * y)
    simpa [mul_assoc] using this
  · intro t g hdom hel
    have hyc : y * (g : DA Δ) = (g : DA Δ) * y := by
      apply Subtype.ext
      funext v
      by_cases hv : v ∈ A.Sg
      · have h1 := hy v hv
        simp [h1]
      · have h1 := hel.2 v hv
        simp [h1]
    have hfin := (dMul F Δ A hA (g : DA Δ) (SD.dS t) hel).1
    have hc : ∀ u ∈ A.dat.U2, ∃ c ∈ A.dat.U2, c * (g : DA Δ) = g * c ∧ u * c⁻¹ ∈ SA Δ ∧ c⁻¹ * u ∈ SA Δ := by
      intro u hu
      obtain ⟨c, hcU, h1, h2, h3⟩ := torPart F Δ A hA u hu
      exact ⟨c, hcU, h3 _ _ hel, h1, h2⟩
    funext h
    rw [Pi.smul_apply]
    unfold SD.lvS
    rw [dc_conj (SA Δ) A.dat.U2 (sa_normal Δ) g y hyc hfin hc φ hφU h, ha t g hdom hel]
    rfl

end
