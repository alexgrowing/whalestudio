import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsUnitPowNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ClsEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KillsComp

theorem proj_pow_eq_one (l : ℕ) [hl : Fact l.Prime] (N : ℕ) [NeZero N] (u : (ZMod N)ˣ)
    (hu : l ∣ N → (l : ℤ) ∣ ((u : ZMod N).val : ℤ) - 1) :
    proj l N u ^ l ^ (N.factorization l - 1) = 1 := by
  set a := N.factorization l
  set m := l ^ (a - 1)
  set U : ℤ := ((u : ZMod N).val : ℤ)
  set e : ℕ := ordCompl[l] N ^ Nat.totient (ordProj[l] N)
  set V : ℤ := (e : ℤ) * U + (1 - (e : ℤ))
  have hV : ((V : ℤ) : ZMod N) = (proj l N u : ZMod N) := by
    simp only [V, proj, projZ, idem, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk, U]
    rw [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hV1 : V - 1 = (e : ℤ) * (U - 1) := by ring
  have htot : 0 < Nat.totient (ordProj[l] N) := Nat.totient_pos.2 (pow_pos hl.out.pos _)
  have hcompl : ((ordCompl[l] N : ℕ) : ℤ) ∣ V ^ m - 1 := by
    have h1 : ((ordCompl[l] N : ℕ) : ℤ) ∣ V - 1 := by
      rw [hV1]
      refine Dvd.dvd.mul_right ?_ _
      exact_mod_cast dvd_pow_self _ htot.ne'
    have h2 : V - 1 ∣ V ^ m - 1 := by simpa using sub_dvd_pow_sub_pow V 1 m
    exact h1.trans h2
  have hproj : ((ordProj[l] N : ℕ) : ℤ) ∣ V ^ m - 1 := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · show ((l ^ a : ℕ) : ℤ) ∣ _
      rw [ha]; simp
    · have hlN : l ∣ N := by
        by_contra h
        have : a = 0 := Nat.factorization_eq_zero_of_not_dvd h
        omega
      have h1 : (l : ℤ) ∣ V - 1 := by
        rw [hV1]; exact Dvd.dvd.mul_left (hu hlN) _
      have := dvd_sub_pow_of_dvd_sub (p := l) (k := a - 1) (by simpa using h1)
      rw [one_pow, Nat.sub_add_cancel ha] at this
      exact_mod_cast this
  have hN : (N : ℤ) ∣ V ^ m - 1 := by
    have hc : IsCoprime ((ordProj[l] N : ℕ) : ℤ) ((ordCompl[l] N : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (coprime_ordProj_ordCompl l N)
    have := hc.mul_dvd hproj hcompl
    rwa [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self] at this
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← hV]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hN
  push_cast at this
  exact sub_eq_zero.1 this

end GlobalTheory.KillsComp

open GlobalTheory.KillsComp in
theorem GlobalTheory.killsMu_comp_of_sq_eq_one : ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N), l ≠ 2 → HV.comp l ψ ^ 2 = 1 → Af.KillsMu (F := ℚ) l (Chr.dirG ℚ Ω (HV.comp l ψ)) := by
  intro Ω _ _ _ l hl O _ N _ ψ hl2 hsq s hs
  set c := Chr.cls ℚ Ω N s
  have hu : l ∣ N → (l : ℤ) ∣ (((c : ZMod N)).val : ℤ) - 1 := by
    intro hlN
    have h1 : Chr.cls ℚ Ω l s = 1 := (Chr.clsFacts ℚ Ω l).2.2.1 s 1 fun ζ hζ => by
      rw [hs ζ hζ, Units.val_one, ZMod.val_one, pow_one]
    have h2 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 l hlN) s
    rw [MonoidHom.comp_apply, h1] at h2
    have h3 := congrArg (fun x : (ZMod l)ˣ => (x : ZMod l)) h2
    simp only [ZMod.unitsMap_val, Units.val_one, ZMod.castHom_apply, ZMod.cast_eq_val] at h3
    have h4 : (((((c : ZMod N)).val : ℤ) - 1 : ℤ) : ZMod l) = 0 := by push_cast; rw [h3]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h4
  have hm := proj_pow_eq_one l N c hu
  set m := l ^ (N.factorization l - 1)
  refine Units.ext ?_
  simp only [Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom, Units.val_one]
  have hval : (HV.comp l ψ) (c : ZMod N) = ψ (proj l N c : ZMod N) := by
    simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  have y2 : ψ (proj l N c : ZMod N) ^ 2 = 1 := by
    have := congrArg (fun χ : DirichletCharacter O N => χ (c : ZMod N)) hsq
    simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
    rwa [hval] at this
  have ym : ψ (proj l N c : ZMod N) ^ m = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hm, Units.val_one, map_one]
  have hcop : Nat.Coprime 2 m := by
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hl2)
  rw [hval]
  have := (pow_gcd_eq_one).2 ⟨y2, ym⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.IrrTransfer

theorem isIrr_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (r' : Γ' →* GL (Fin n) k) (h : ∀ g', ∃ g, r g = r' g') (hr' : Af.IsIrr r') : Af.IsIrr r := by
  unfold Af.IsIrr IsIrrSub at *
  obtain ⟨h1, h2, h3⟩ := hr'
  refine ⟨h1, fun g v _ => Submodule.mem_top, fun W' hle hW => h3 W' hle ?_⟩
  intro g' v hv
  obtain ⟨g, hg⟩ := h g'
  rw [← hg]
  exact hW g v hv

end GlobalTheory.Ord2.IrrTransfer

theorem GlobalTheory.Ord2.irr_transfer : ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] (η : G ℚ Ω →* ℤˣ), η.ker = Base.galOf ℚ K Ω → ∀ W : R2 Ω l, (∀ g, (mat W g).det = ((η g : ℤˣ) : ℤ)) → Af.IsIrr ((W.comp (Base.galEmb ℚ K Ω)).comp (cycBar K Ω l).ker.subtype) → Af.IsIrr (W.comp (H0g W).subtype) := by
  intro Ω _ _ _ K _ _ _ l _ η hη W hdet hirr
  refine GlobalTheory.Ord2.IrrTransfer.isIrr_of_range _ _ ?_ hirr
  rintro ⟨τ, hτ⟩
  have hmem : Base.galEmb ℚ K Ω τ ∈ H0g W := by
    refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_, MonoidHom.mem_ker.2 ?_⟩
    · exact (MonoidHom.mem_ker.1 hτ : _)
    · have hm : Base.galEmb ℚ K Ω τ ∈ η.ker := hη ▸ Base.galEmb_mem ℚ K Ω τ
      rw [MonoidHom.mem_ker] at hm
      apply Units.ext
      have := hdet (Base.galEmb ℚ K Ω τ)
      rw [hm] at this
      simpa [dt] using this
  exact ⟨⟨_, hmem⟩, rfl⟩

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem cls_eq_one' {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) : Chr.cls ℚ Ω N g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h1 := Chr.cls_spec N g ζ hζ.pow_eq_one
  rw [hg ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ (1 : ZMod N).val = ζ := by
    rw [ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2.symm)

open UpperTheory.V.U3 in
private theorem block_form' {k : Type} [Field k] (X : Matrix (Fin 3) (Fin 3) k) (Y : Matrix (Fin 2) (Fin 2) k)
    (hb : ∀ a b, Odd (wt a b) → X a b = 0) (h1 : X 1 1 = 1) (hY : Y = corner X) :
    X = !![Y 0 0, 0, Y 0 1; 0, 1, 0; Y 1 0, 0, Y 1 1] := by
  subst hY
  have e01 := hb 0 1 (by decide)
  have e10 := hb 1 0 (by decide)
  have e12 := hb 1 2 (by decide)
  have e21 := hb 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corner, e01, e10, e12, e21, h1]

open UpperTheory.V.U3 in
private theorem conj_mat' {Γ k : Type} [Group Γ] [Field k] (M : GL (Fin 3) k) (r : Γ →* GG 3 k) (g : Γ)
    (hg : (r g).right = 1) : (conjBy M r g).mat = (M : Matrix (Fin 3) (Fin 3) k) * (r g).mat * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  simp [conjBy, GG.mat, hg]

open UpperTheory.V.U3 in
private theorem eigvec' {k : Type} [Field k] (M : GL (Fin 3) k) (X : Matrix (Fin 3) (Fin 3) k) (a : k)
    (h0 : ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a)
    (h : ∀ i j, wt i j < 0 → ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) i j = 0) :
    X *ᵥ (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) =
      a • (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) := by
  have e : ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) *ᵥ Pi.single 0 1 =
      a • Pi.single 0 1 := by
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h 1 0 (by decide)
    · simpa using h 2 0 (by decide)
  rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

open UpperTheory.V.Base UpperTheory.V.U3 Matrix in
theorem levelAway_block : U3.CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* U3.GG 3 (PadicAlgCl l)} (_ : D.IsPt U g₁ r), U3.TypeII D.η r → ∀ W : R2 Ω l, D.IsExt r W → (∀ g, (mat W g).det = ((D.η g : ℤˣ) : ℤ)) → ∃ M : ℕ, 1 ≤ M ∧ Af.LevelAway l M W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h hII W hext hdet
  have h11 := (typeII_facts hC D hM h hII).1
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      rw [cls_eq_one' N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg =>
    block_form' _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)
  refine ⟨N * (discr K).natAbs, Nat.mul_pos (NeZero.pos N) hodd.pos, fun w hw => ?_⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
  obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
  have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
    have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
    have hc' : cycBar ℚ Ω l g = 1 := by
      rw [cycBar, MonoidHom.comp_apply, hc, map_one]
    rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
    congr 2
    funext i
    fin_cases i <;> simp [wt1]
  obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
  exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩

open UpperTheory.V.Base UpperTheory.V.U3 Matrix in
theorem flag_block : U3.CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* U3.GG 3 (PadicAlgCl l)} (_ : D.IsPt U g₁ r), U3.TypeII D.η r → ∀ W : R2 Ω l, D.IsExt r W → (∀ g, (mat W g).det = ((D.η g : ℤˣ) : ℤ)) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ, Af.IsFlagOn W (Dec (F := ℚ) A) κ ∧ ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = D.ΨQ s ∧ κ 1 s = (D.ΨQ s)⁻¹ := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h hII W hext hdet A hAl
  have h11 := (typeII_facts hC D hM h hII).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg =>
    block_form' _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)
  obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
  obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
  obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
  have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
    have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
    rw [map_sub, map_pow, map_one, sub_ne_zero] at this
    exact this
  set v : Fin 3 → Qbar l := ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := fun h0 => by
    have := congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simp at this
  have hev : ∀ s ∈ Ine (F := ℚ) A,
      !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
    have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
    rw [← hblk s (hIk hs)]
    refine eigvec' M _ _ ?_ fun i j hij => ?_
    · rw [← conj_mat' M r s hr, hdiag s hs 0]
      simp [GG.mat, tor_val, wt1]
    · rw [← conj_mat' M r s hr]
      exact hup s (hID hs) (hIk hs) i j hij
  have hv1 : v 1 = 0 := by
    have := congrFun (hev s₀ hs₀) 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    by_contra hne
    have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
    exact hs₀' (by rw [h3, one_pow])
  obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
    (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
    (fun h0 => hv0 (by
      funext i
      fin_cases i
      · exact congrFun h0 0
      · exact hv1
      · exact congrFun h0 1))
    (fun s hs => by
      have a0 := congrFun (hev s hs) 0
      have a2 := congrFun (hev s hs) 2
      funext i
      fin_cases i
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
    (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
    ⟨s₀, hs₀, hs₀'⟩
  exact ⟨κ, hflag, hκ⟩

open UpperTheory.V.Base UpperTheory.V.U3 in
theorem conj_eta {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ)
    (s : G ℚ Ω) (hs : IsConj s) : D.η s = -1 := by
  obtain ⟨φ, hφ⟩ := hs
  have himag := D.gd.imag
  refine (Int.units_eq_one_or _).resolve_left fun h => ?_
  have h1 : s ∈ galOf ℚ K Ω := D.η_ker ▸ h
  refine IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hφ, h1 x]

open UpperTheory.V.Base UpperTheory.V.U3 in
theorem psi_ine {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) :
    ∀ g ∈ Loc.Iq l, Chr.dirG ℚ Ω ψ (D.ι g) = Chr.dirG ℚ Ω (HV.comp l ψ) (D.ι g) := by
  intro g hg
  obtain ⟨-, -, -, -, -, -, hcyc, -⟩ := dat_loc D
  have h1 := D.Ψ_I g hg
  have h2 : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (D.ι g) = chiO ℚ Ω l c.O (D.ι g) ^ (e : ℤ) * Chr.dirG ℚ Ω ψ (D.ι g) := rfl
  have h3 : chiO ℚ Ω l c.O (D.ι g) = Loc.cycA l l c.O g := by
    show Units.map _ (cycZ ℚ Ω l (D.ι g)) = _
    rw [hcyc]
    rfl
  rw [h2, h3, zpow_natCast] at h1
  exact mul_left_cancel h1

open UpperTheory.V.Base UpperTheory.V.U3 in

theorem admissible_of_type_two_block : U3.CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* U3.GG 3 (PadicAlgCl l)} (_ : D.IsPt U g₁ r) (ι : Qbar l ≃+* ℂ), U3.TypeII D.η r → ∀ W : R2 Ω l, D.IsExt r W → Continuous W → (∀ g, (mat W g).det = ((D.η g : ℤˣ) : ℤ)) → D.IsModular ι W → admitted ι e W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII W hext hcont hdet hmod
  have hdt : ∀ g, (dt W g : Qbar l) = ((D.η g : ℤˣ) : ℤ) := fun g => hdet g
  obtain ⟨A, hA, -, hIA, -, -, -, -⟩ := dat_loc D
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  obtain ⟨hIk, -⟩ := hl1 A hA
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  let χ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω (HV.comp l ψ))
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hχ2 : ∀ g, χ g * χ g = 1 := fun g => by
    have h1 : Chr.dirG ℚ Ω (HV.comp l ψ) g * Chr.dirG ℚ Ω (HV.comp l ψ) g = 1 := by
      apply Units.ext
      show (HV.comp l ψ) (Chr.cls ℚ Ω N g) * (HV.comp l ψ) (Chr.cls ℚ Ω N g) = 1
      rw [← MulChar.mul_apply, ← sq, D.gd.ine, MulChar.one_apply (Units.isUnit _)]
    show Units.map _ _ * Units.map _ _ = 1
    rw [← map_mul, h1, map_one]
  have hψχ : ∀ s ∈ Ine (F := ℚ) A, ψQ s = χ s := fun s hs => by
    rw [← hIA] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    show Units.map _ _ = Units.map _ _
    rw [psi_ine D g hg]
  obtain ⟨κ, hflag, hκ⟩ := flag_block hC D hM h hII W hext hdet A hA
  refine ⟨hcont, ?_, fun s hs => Units.ext ?_, GlobalTheory.Ord2.irr_transfer D.η D.η_ker W hdet (typeII_irr_cyc hC D hM h hII W hext),
    levelAway_block hC D hM h hII W hext hdet, ?_, A, χ, κ, ?_, fun s hs => ?_, hflag, fun s hs => ?_, fun s hs => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [MonoidHom.one_apply, Units.val_one, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hdt]
    rcases Int.units_eq_one_or (D.η g) with h1 | h1 <;> simp [h1]
  · rw [hdt, conj_eta D s hs]
    simp
  · obtain ⟨f, hf⟩ := hmod
    refine ⟨f, 1, 1, le_rfl, fun _ _ => rfl, ?_⟩
    rw [mul_one]
    exact hf
  · obtain ⟨h1, h2, h3, -⟩ := places ℚ Ω l A
    have hne : A ≠ ⊤ := fun ht => (h2 ht).2 hA
    obtain ⟨v, hv⟩ := h1 hne
    exact ⟨v, hv, (h3 v hv).1 hA⟩
  · show Units.map _ _ = 1
    rw [GlobalTheory.killsMu_comp_of_sq_eq_one ψ D.gd.l_odd D.gd.ine s hs, map_one]
  · rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hdt, hIk hs]
    simp
  · rw [(hκ s hs).1, (hκ s hs).2, hΨ, hψχ s hs, mul_inv, ← zpow_neg]
    refine ⟨rfl, ?_⟩
    congr 1
    exact inv_eq_of_mul_eq_one_right (hχ2 s)

end GlobalTheory.Ord2

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem tw_coe (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    mat (tw W χ) s = (χ s : Qbar l) • mat W s := tw_val W χ s

theorem dt_coe (W : R2 Ω l) (s : G ℚ Ω) : (dt W s : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem dt_tw (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) : dt (tw W χ) = χ ^ 2 * dt W := by
  ext s
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
  rw [dt_coe, dt_coe, tw_coe, Matrix.det_smul]
  simp

theorem killsMu_dvd {M N : ℕ} {C : Type} [Monoid C] {χ : G ℚ Ω →* C} (h : KillsMu M χ) (hMN : M ∣ N) :
    KillsMu N χ := by
  intro s hs
  apply h s
  intro ζ hζ
  obtain ⟨k, rfl⟩ := hMN
  exact hs ζ (by rw [pow_mul, hζ, one_pow])

theorem killsMu_mul {M : ℕ} {C : Type} [CommMonoid C] {χ ψ : G ℚ Ω →* C} (h : KillsMu M χ) (h' : KillsMu M ψ) :
    KillsMu M (χ * ψ) := by
  intro s hs
  simp [h s hs, h' s hs]

end GlobalTheory.Ord2.TwDet

namespace GlobalTheory.Ord2.TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cont_val {W : R2 Ω l} (h : Continuous W) : Continuous fun s => mat W s :=
  Units.continuous_val.comp h

theorem dt_cont {W : R2 Ω l} (h : Continuous W) : Continuous fun s => (dt W s : Qbar l) := by
  simp_rw [dt_coe]
  exact (cont_val h).matrix_det

theorem tw_cont {W : R2 Ω l} {χ : G ℚ Ω →* (Qbar l)ˣ} (h : Continuous W)
    (hχ : Continuous fun s => (χ s : Qbar l)) : Continuous (tw W χ) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun s => mat (tw W χ) s
    simp_rw [tw_coe]
    exact hχ.smul (cont_val h)
  · have e : ∀ s, (((tw W χ s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = mat (tw W χ) s⁻¹ := by
      intro s; simp only [mat, map_inv]
    simp_rw [e, tw_coe]
    exact (hχ.comp continuous_inv).smul ((cont_val h).comp continuous_inv)

theorem ker_open {W : R2 Ω l} (h : Continuous W) (h2 : dt W ^ 2 = 1) : IsOpen ((dt W).ker : Set (G ℚ Ω)) := by
  have hs : ((dt W).ker : Set (G ℚ Ω)) = {s | (dt W s : Qbar l) = -1}ᶜ := by
    ext s
    have hsq : (dt W s : Qbar l) * (dt W s : Qbar l) = 1 := by
      have := congrArg (fun f : G ℚ Ω →* (Qbar l)ˣ => ((f s : (Qbar l)ˣ) : Qbar l)) h2
      simpa [pow_two] using this
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h1 h2
      rw [h1] at h2
      have : (1 : Qbar l) = -1 := by simpa using h2
      have h2' : (2 : Qbar l) = 0 := by linear_combination this
      exact two_ne_zero h2'
    · intro hne
      rcases mul_self_eq_one_iff.mp hsq with h1 | h1
      · exact Units.val_eq_one.mp h1
      · exact absurd h1 hne
  rw [hs, isOpen_compl_iff]
  exact isClosed_eq (dt_cont h) continuous_const

end GlobalTheory.Ord2.TwDet

namespace GlobalTheory.Ord2.TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem tw_tw (W : R2 Ω l) (a b : G ℚ Ω →* (Qbar l)ˣ) : tw (tw W a) b = tw W (b * a) := by
  ext s i j
  change mat (tw (tw W a) b) s i j = mat (tw W (b * a)) s i j
  rw [tw_coe, tw_coe, tw_coe]
  simp [smul_smul, mul_assoc]

theorem conj_tw (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (g : GL (Fin 2) (Qbar l)) (s : G ℚ Ω) :
    ((g * tw W χ s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) =
      (χ s : Qbar l) • ((g * W s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
  simp only [Units.val_mul]
  change (g : Matrix (Fin 2) (Fin 2) (Qbar l)) * mat (tw W χ) s * _ = _
  rw [tw_coe, Matrix.mul_smul, Matrix.smul_mul]

theorem dt_conj (W : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (s : G ℚ Ω) :
    (dt W s : Qbar l) = ((g * W s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, inv_mul_cancel, one_mul]
  rfl

theorem diag_tw {W : R2 Ω l} {H : Subgroup (G ℚ Ω)} {χ : Fin 2 → G ℚ Ω →* (Qbar l)ˣ} (h : IsDiagOn W H χ) :
    IsDiagOn (tw W (dt W)) H (fun i => χ i * χ 0 * χ 1) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s hs => ?_⟩
  have hd : (dt W s : Qbar l) = (χ 0 s : Qbar l) * (χ 1 s : Qbar l) := by
    rw [dt_conj W g s, hg s hs, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [conj_tw, hg s hs, hd]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.diagonal_apply]; ring
  · simp [Matrix.diagonal_apply, hij]

theorem flag_tw {W : R2 Ω l} {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ} (h : IsFlagOn W H κ) :
    IsFlagOn (tw W (dt W)) H (fun i => κ i * (dt W).comp H.subtype) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · rw [conj_tw, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
  · rw [conj_tw, Matrix.smul_apply, (hg s).2 i]
    simp [mul_comm]

end GlobalTheory.Ord2.TwDet

namespace GlobalTheory.Ord2

open TwDet

theorem admissible_twist_by_det : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (e : ℕ) (W : R2 Ω l), admitted ι e W → admitted ι e (tw W (dt W)) := by
  intro l _ Ω _ _ _ ι e W h
  have hdt : dt (tw W (dt W)) = dt W := by rw [dt_tw, h.det2, one_mul]
  obtain ⟨N, hN, hNk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2)
    (Abelianization.commutator_subset_ker (dt W))
  have hθN : KillsMu N (dt W) := fun s hs => hNk s hs
  refine ⟨tw_cont h.cont (dt_cont h.cont), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdt]; exact h.det2
  · intro s hs; rw [hdt]; exact h.odd s hs
  · have hH : H0g (tw W (dt W)) = H0g W := by unfold H0g; rw [hdt]
    rw [hH]
    have : (tw W (dt W)).comp (H0g W).subtype = W.comp (H0g W).subtype := by
      ext s i j
      change mat (tw W (dt W)) s i j = mat W s i j
      have h1 : dt W (s : G ℚ Ω) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp s.2).2
      rw [tw_coe, h1]
      simp
    rw [this]; exact h.irr
  · obtain ⟨M, hM, hl⟩ := h.away
    refine ⟨M, hM, fun w hw => ?_⟩
    obtain ⟨A, hA, χ, hχ, hd⟩ := hl w hw
    exact ⟨A, hA, fun i => χ i * χ 0 * χ 1,
      fun i => killsMu_mul (killsMu_mul (hχ i) (hχ 0)) (hχ 1), diag_tw hd⟩
  · obtain ⟨f, M, φ, hM, hφ, hf⟩ := h.modular
    refine ⟨f, M * N, φ * dt W, Nat.mul_pos hM hN,
      killsMu_mul (killsMu_dvd hφ (dvd_mul_right M N)) (killsMu_dvd hθN (dvd_mul_left N M)), ?_⟩
    rw [tw_tw, mul_assoc, mul_assoc, ← pow_two, h.det2, mul_one]
    exact hf
  · obtain ⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩ := h.flag
    refine ⟨A, χ, fun i => κ i * (dt W).comp (Dec (F := ℚ) A).subtype, hA, hχ, flag_tw hfl, ?_, ?_⟩
    · rw [hdt]; exact hine
    · intro s hs
      have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
      obtain ⟨h0, h1'⟩ := hk s hs
      refine ⟨?_, ?_⟩ <;>
        simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, h1, mul_one] <;>
        assumption

end GlobalTheory.Ord2

end
