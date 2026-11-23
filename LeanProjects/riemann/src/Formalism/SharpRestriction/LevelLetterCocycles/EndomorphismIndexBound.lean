import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.CharacterColumnKernels.Assemble
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CongMem
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.BridgeDet
import Formalism.CharacterColumnKernels.IdempotentNormalForms.IsUnitDetOfConst
import Formalism.CharacterColumnKernels.StatLowestInZ
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelLengthBound
import Formalism.CharacterColumnKernels.IdempotentNormalForms.MemCcIdealIffForall
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SumIteLe
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SplitFibre
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SpacedProductLowerBound
import Formalism.CharacterColumnKernels.IdempotentNormalForms.IdemNormalForm
import Mathlib
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SmulEqZeroIffCrit

noncomputable section

open Module IsDiscreteValuationRing Formalism.BasicNotions

namespace Formalism.MainNotions.TruncatedSeriesCountingIdentities

namespace Br

section Quot

variable {O : Type*} [CommRing O] {V : Type*} [AddCommGroup V] [Module O V]

theorem quot_le (L A B : Submodule O V) (P : V →ₗ[O] V) (hA : ∀ v ∈ A, P v = v)
    (hB : ∀ v ∈ B, P v = 0) (hPA : ∀ v, P v ∈ A) (hPB : ∀ v, v - P v ∈ B) :
    Module.length O (↥((L ⊔ B) ⊓ A) ⧸ (L ⊓ A).comap ((L ⊔ B) ⊓ A).subtype) ≤
      Module.length O (↥L ⧸ ((A ⊓ L) ⊔ (B ⊓ L)).comap L.subtype) := by
  have hmem : ∀ v : ↥L, P v ∈ (L ⊔ B) ⊓ A := by
    intro v
    refine Submodule.mem_inf.mpr ⟨?_, hPA v⟩
    have h1 : (v : V) ∈ L ⊔ B := Submodule.mem_sup_left v.2
    have h2 : (v : V) - P v ∈ L ⊔ B := Submodule.mem_sup_right (hPB v)
    have h3 := Submodule.sub_mem _ h1 h2
    simpa using h3
  let g : ↥L →ₗ[O] ↥((L ⊔ B) ⊓ A) := LinearMap.codRestrict ((L ⊔ B) ⊓ A) (P ∘ₗ L.subtype) hmem
  let q := (Submodule.mkQ ((L ⊓ A).comap ((L ⊔ B) ⊓ A).subtype)) ∘ₗ g
  have hK : ((A ⊓ L) ⊔ (B ⊓ L)).comap L.subtype ≤ LinearMap.ker q := by
    intro v hv
    rw [Submodule.mem_comap] at hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show P v ∈ L ⊓ A
    have hv' : (v : V) = a + b := hab.symm
    rw [hv', map_add, hA a (Submodule.mem_inf.mp ha).1, hB b (Submodule.mem_inf.mp hb).1, add_zero]
    exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp ha).2, (Submodule.mem_inf.mp ha).1⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨hwLB, hwA⟩ := Submodule.mem_inf.mp w.2
    obtain ⟨l, hl, b, hb, hlb⟩ := Submodule.mem_sup.mp hwLB
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [LinearMap.comp_apply]
    congr 1
    apply Subtype.ext
    show P l = (w : V)
    have hPw : P (w : V) = w := hA w hwA
    rw [← hPw, ← hlb, map_add, hB b hb, add_zero]
  refine Module.length_le_of_surjective (Submodule.liftQ _ q hK) ?_
  intro y
  obtain ⟨v, rfl⟩ := hq y
  exact ⟨Submodule.Quotient.mk v, Submodule.liftQ_apply _ _ _⟩

end Quot

section Bump

variable {O : Type*} [CommRing O] [IsDomain O] {X : Type*} [Fintype X] [DecidableEq X]
  (T : Subalgebra O (X → O))

theorem coe_prod' {ι : Type*} (s : Finset ι) (h : ι → T) (z : X) :
    ((∏ y ∈ s, h y : T) : X → O) z = ∏ y ∈ s, ((h y : T) : X → O) z := by
  first
  | rw [SubmonoidClass.coe_finsetProd, Finset.prod_apply]
  | simp [Finset.prod_apply]

theorem coe_sum' {ι : Type*} (s : Finset ι) (h : ι → T) (z : X) :
    ((∑ y ∈ s, h y : T) : X → O) z = ∑ y ∈ s, ((h y : T) : X → O) z := by
  first
  | rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
  | simp [Finset.sum_apply]

theorem exists_bump (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g : T, (g : X → O) x ≠ 0 ∧ ∀ y, y ≠ x → (g : X → O) y = 0 := by
  classical
  choose f hfT hf using fun y : {y : X // y ≠ x} => hsep x y.1 (Ne.symm y.2)
  let h : {y : X // y ≠ x} → T := fun y => ⟨f y, hfT y⟩ - algebraMap O T (f y y.1)
  have hev : ∀ y z, ((h y : T) : X → O) z = f y z - f y y.1 := by
    intro y z
    simp [h]
  refine ⟨∏ y, h y, ?_, ?_⟩
  · rw [coe_prod' T]
    exact Finset.prod_ne_zero_iff.mpr fun y _ => by rw [hev]; exact sub_ne_zero.mpr (hf y)
  · intro y hy
    rw [coe_prod' T]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) (by rw [hev]; exact sub_self _)

theorem exists_ind (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) :
    ∃ C : O, C ≠ 0 ∧ ∀ S : Finset X, ∃ e : T, ∀ y, (e : X → O) y = if y ∈ S then C else 0 := by
  classical
  choose g hgx hgy using fun x => exists_bump T hsep x
  refine ⟨∏ x, (g x : X → O) x, Finset.prod_ne_zero_iff.mpr fun x _ => hgx x, fun S => ?_⟩
  refine ⟨∑ x ∈ S, g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x'), fun y => ?_⟩
  rw [coe_sum' T]
  have hterm : ∀ x, ((g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x') : T) :
      X → O) y = if y = x then ∏ x, (g x : X → O) x else 0 := by
    intro x
    have hc : ((g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x') : T) :
        X → O) y = (g x : X → O) y * ∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x' := by
      simp
    rw [hc]
    split_ifs with hxy
    · subst hxy
      exact Finset.mul_prod_erase Finset.univ (fun x' => (g x' : X → O) x') (Finset.mem_univ _)
    · rw [hgy x y hxy, zero_mul]
  simp only [hterm]
  rw [Finset.sum_ite_eq]

end Bump

section Main

open Formalism.NG Formalism.NG.QuotientPowerLengths

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

def actK : T →ₐ[O] Module.End (FractionRing O) (TensorProduct O (FractionRing O) M) :=
  (Module.End.baseChangeHom O (FractionRing O) M).comp act

theorem actK_apply (f : T) : actK T act f = (act f).baseChange (FractionRing O) := rfl

theorem heckeEig_eq (x : X) :
    heckeEig T act x = Vx T (actK T act).toRingHom x := by
  unfold Formalism.BasicNotions.heckeEig Formalism.NG.Vx
  refine iInf_congr fun f => ?_
  ext v
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  simp [actK_apply, sub_eq_zero]

theorem mul_ind [DecidableEq X] {C : O} {x : X} {e : T}
    (he : ∀ y, (e : X → O) y = if y ∈ ({x} : Finset X) then C else 0) (f : T) :
    f * e = ((f : X → O) x) • e := by
  apply Subtype.ext
  funext y
  show (f : X → O) y * (e : X → O) y = (f : X → O) x * (e : X → O) y
  rw [he y]
  split_ifs with h
  · rw [Finset.mem_singleton.mp h]
  · simp

theorem eigSpan (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) :
    (⨆ x, Vx T (actK T act).toRingHom x) = ⊤ := by
  classical
  obtain ⟨C, hC, hind⟩ := exists_ind T hsep
  choose e he using fun x : X => hind {x}
  have hsum : ∑ x, e x = algebraMap O T C := by
    apply Subtype.ext
    funext y
    rw [coe_sum' T]
    simp [he]
  have hmemV : ∀ x (v : TensorProduct O (FractionRing O) M),
      actK T act (e x) v ∈ Vx T (actK T act).toRingHom x := by
    intro x v
    unfold Formalism.NG.Vx
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [LinearMap.mem_ker]
    have hm := mul_ind T (he x) f
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Module.End.mul_apply, ← map_mul, hm, map_smul, LinearMap.smul_apply, algebraMap_smul,
      sub_self]
  rw [eq_top_iff]
  intro v _
  have hCK : algebraMap O (FractionRing O) C ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hC
  have hv : algebraMap O (FractionRing O) C • v = ∑ x, actK T act (e x) v := by
    rw [← LinearMap.sum_apply, ← map_sum, hsum, AlgHom.commutes, Module.algebraMap_end_apply,
      algebraMap_smul]
  have h1 : algebraMap O (FractionRing O) C • v ∈ ⨆ x, Vx T (actK T act).toRingHom x := by
    rw [hv]
    exact Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (hmemV x v)
  have h2 := Submodule.smul_mem _ (algebraMap O (FractionRing O) C)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hCK, one_smul] at h2

theorem len_le (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (L : Submodule O (TensorProduct O (FractionRing O) M)) (S : Finset X) :
    Module.length O
      (↥((L ⊔ (VS T (actK T act).toRingHom (S : Set X)ᶜ).restrictScalars O) ⊓
          (VS T (actK T act).toRingHom (S : Set X)).restrictScalars O) ⧸
        (L ⊓ (VS T (actK T act).toRingHom (S : Set X)).restrictScalars O).comap
          ((L ⊔ (VS T (actK T act).toRingHom (S : Set X)ᶜ).restrictScalars O) ⊓
            (VS T (actK T act).toRingHom (S : Set X)).restrictScalars O).subtype) ≤
      Module.length O (CongMod T (actK T act).toRingHom L (S : Set X)) := by
  classical
  obtain ⟨C, hC, hind⟩ := exists_ind T hsep
  choose e he using fun x : X => hind {x}
  have hsumAll : ∑ x, e x = algebraMap O T C := by
    apply Subtype.ext
    funext y
    rw [coe_sum' T]
    simp [he]
  have hfun : ∀ (s : Finset X) y, ((∑ x ∈ s, e x : T) : X → O) y = if y ∈ s then C else 0 := by
    intro s y
    rw [coe_sum' T]
    simp [he]
  have hmemV : ∀ x (v : TensorProduct O (FractionRing O) M),
      actK T act (e x) v ∈ Vx T (actK T act).toRingHom x := by
    intro x v
    unfold Formalism.NG.Vx
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [LinearMap.mem_ker]
    have hm := mul_ind T (he x) f
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Module.End.mul_apply, ← map_mul, hm, map_smul, LinearMap.smul_apply, algebraMap_smul,
      sub_self]
  have hvx : ∀ x (f : T) (v : TensorProduct O (FractionRing O) M),
      v ∈ Vx T (actK T act).toRingHom x →
        actK T act f v = algebraMap O (FractionRing O) ((f : X → O) x) • v := by
    intro x f v hv
    unfold Formalism.NG.Vx at hv
    have h := (Submodule.mem_iInf _).mp hv f
    rw [LinearMap.mem_ker] at h
    simpa [sub_eq_zero] using h
  have hcK : algebraMap O (FractionRing O) C ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hC
  have hAle : VS T (actK T act).toRingHom (S : Set X) ≤
      LinearMap.ker (actK T act (∑ x ∈ S, e x) - algebraMap O (FractionRing O) C • LinearMap.id) := by
    unfold Formalism.NG.VS
    refine iSup₂_le fun x hx => ?_
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hvx x _ v hv, hfun S x,
      if_pos (Finset.mem_coe.mp hx)]
    simp
  have hBle : VS T (actK T act).toRingHom ((S : Set X)ᶜ) ≤
      LinearMap.ker (actK T act (∑ x ∈ S, e x)) := by
    unfold Formalism.NG.VS
    refine iSup₂_le fun x hx => ?_
    intro v hv
    have hx' : x ∉ S := fun h => hx (Finset.mem_coe.mpr h)
    rw [LinearMap.mem_ker, hvx x _ v hv, hfun S x, if_neg hx']
    simp
  have hPA' : ∀ v, actK T act (∑ x ∈ S, e x) v ∈ VS T (actK T act).toRingHom (S : Set X) := by
    intro v
    rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    unfold Formalism.NG.VS
    exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (Finset.mem_coe.mpr hx) (hmemV x v))
  have hrest : ∀ v, actK T act (∑ x ∈ Finset.univ \ S, e x) v ∈
      VS T (actK T act).toRingHom ((S : Set X)ᶜ) := by
    intro v
    rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx' : x ∈ ((S : Set X)ᶜ) := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_coe.mp h)
    unfold Formalism.NG.VS
    exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx' (hmemV x v))
  have hcv : ∀ v, algebraMap O (FractionRing O) C • v =
      actK T act (∑ x ∈ Finset.univ \ S, e x) v + actK T act (∑ x ∈ S, e x) v := by
    intro v
    rw [← LinearMap.add_apply, ← map_add, Finset.sum_sdiff (Finset.subset_univ S), hsumAll,
      AlgHom.commutes, Module.algebraMap_end_apply, algebraMap_smul]
  have hPB' : ∀ v, v - (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v ∈
      VS T (actK T act).toRingHom ((S : Set X)ᶜ) := by
    intro v
    have h1 : v - (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v =
        (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ Finset.univ \ S, e x) v := by
      rw [eq_inv_smul_iff₀ hcK, smul_sub, hcv v, smul_smul, mul_inv_cancel₀ hcK, one_smul,
        add_sub_cancel_right]
    rw [h1]
    exact Submodule.smul_mem _ _ (hrest v)
  let P : TensorProduct O (FractionRing O) M →ₗ[O] TensorProduct O (FractionRing O) M :=
    ((algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x)).restrictScalars O
  refine quot_le L _ _ P ?_ ?_ ?_ ?_
  · intro v hv
    have h := hAle hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v = v
    rw [h, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  · intro v hv
    have h := LinearMap.mem_ker.mp (hBle hv)
    show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v = 0
    rw [h, smul_zero]
  · intro v
    show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v ∈
      VS T (actK T act).toRingHom (S : Set X)
    exact Submodule.smul_mem _ _ (hPA' v)
  · intro v
    exact hPB' v

theorem mem_ccIdeal_iff (Z : Finset X) (f : T) :
    f ∈ Formalism.BasicNotions.ccIdeal T Z ↔ f ∈ Formalism.NG.ccIdeal T (Z : Set X) := by
  simp only [Formalism.BasicNotions.ccIdeal, Formalism.NG.ccIdeal, Formalism.NG.resOff, RingHom.mem_ker]
  rw [funext_iff, funext_iff]
  constructor
  · intro h y
    exact h ⟨y.1, y.2⟩
  · intro h y
    exact h ⟨y.1, y.2⟩

theorem length_ccAt (Z : Finset X) (π : X) :
    Module.length O (O ⧸ ccAt T Z π) = vcc T (Z : Set X) π := by
  obtain ⟨c, hc, hval⟩ := vcc_attain (T := T) (Z : Set X) π
  have h : ccAt T Z π = Ideal.span {(c : X → O) π} := by
    apply le_antisymm
    · rw [ccAt, Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      show (c : X → O) π ∣ (f : X → O) π
      rw [← addVal_le_iff_dvd, hval]
      exact iInf₂_le f ((mem_ccIdeal_iff T Z f).mp hf)
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_map_of_mem _ ((mem_ccIdeal_iff T Z c).mpr hc)
  rw [h, IdempotentNormalFormsLenFacts.length_quot_span, hval]

theorem vcc_ne_top (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z : Finset X) (π : X)
    (hπ : π ∈ Z) : vcc T (Z : Set X) π ≠ ⊤ := by
  classical
  obtain ⟨C, hC, hind⟩ := exists_ind T hsep
  obtain ⟨e, he⟩ := hind {π}
  have heI : e ∈ Formalism.NG.ccIdeal T (Z : Set X) := by
    simp only [Formalism.NG.ccIdeal, RingHom.mem_ker]
    funext y
    have hy : y.1 ≠ π := fun h => y.2 (by rw [Finset.mem_coe, h]; exact hπ)
    show (e : X → O) y.1 = 0
    rw [he, if_neg (by simpa using hy)]
  have hle : vcc T (Z : Set X) π ≤ IsDiscreteValuationRing.addVal O ((e : X → O) π) := by
    unfold Formalism.NG.vcc
    exact iInf₂_le e heI
  intro htop
  rw [htop, top_le_iff, he, if_pos (Finset.mem_singleton_self π)] at hle
  exact hC ((IsDiscreteValuationRing.addVal_eq_top_iff).mp hle)

theorem addVal_int (l : ℕ) [Fact l.Prime] (hl : ¬ IsUnit (l : O)) (A : ℤ) (hA : A ≠ 0) :
    addVal O (A : O) = (padicValInt l A : ℕ∞) * addVal O (l : O) := by
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
  obtain ⟨m, hm⟩ : (l : ℤ) ^ padicValInt l A ∣ A := (padicValInt_dvd_iff _ A).mpr (Or.inr le_rfl)
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨m', hm'⟩
    have h2 : (l : ℤ) ^ (padicValInt l A + 1) ∣ A :=
      Dvd.intro m' (by rw [pow_succ, mul_assoc, ← hm']; exact hm.symm)
    rcases (padicValInt_dvd_iff (padicValInt l A + 1) A).mp h2 with h | h
    · exact hA h
    · omega
  have hcop : IsCoprime (l : ℤ) m := (Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hnd
  obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom O)
  have hmu : IsUnit (m : O) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one huv with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) (by simpa using hl)
    · simpa using isUnit_of_mul_isUnit_right h
  obtain ⟨w, hw⟩ := hmu
  conv_lhs => rw [hm]
  push_cast
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, ← hw,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit, add_zero, nsmul_eq_mul]

def latIn (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] :
    Submodule O (TensorProduct O (FractionRing O) M) :=
  LinearMap.range (TensorProduct.mk O (FractionRing O) M 1)

theorem baseChange_latIn (β : Module.End O M) :
    ∀ v ∈ latIn O M, β.baseChange (FractionRing O) v ∈ latIn O M := by
  intro v hv
  obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hv
  exact LinearMap.mem_range.mpr ⟨β m, by simp [LinearMap.baseChange_tmul]⟩

theorem span_latIn : Submodule.span (FractionRing O) (latIn O M : Set (TensorProduct O (FractionRing O) M)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
    have ht : a ⊗ₜ[O] m = a • ((1 : FractionRing O) ⊗ₜ[O] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (LinearMap.mem_range.mpr ⟨m, rfl⟩ : (1 : FractionRing O) ⊗ₜ[O] m ∈ latIn O M))
  | add x y hx hy => exact add_mem hx hy

theorem fg_latIn : (latIn O M).FG := by
  unfold latIn
  rw [LinearMap.range_eq_map]
  exact (Module.Finite.fg_top).map _

theorem hecke_length_bound [IsLocalRing T] (l : ℕ) [Fact l.Prime]
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z Z' : Finset X) (hZ' : Z' ⊆ Z)
    (α : Module.End O M) (A : ℤ) (hA : A ≠ 0) (hcomm : ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ Z', ∀ u ∈ heckeEig T act x,
      α.baseChange (FractionRing O) u = (A : FractionRing O) • u)
    (h0 : ∀ x ∈ Z, x ∉ Z' → ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = 0) :
    lenUnit (O := O) l
        (↥((latIn O M ⊔ (⨆ x ∈ (Z' : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
            (⨆ x ∈ (Z' : Set X), heckeEig T act x).restrictScalars O) ⧸
          (latIn O M ⊓ (⨆ x ∈ (Z' : Set X), heckeEig T act x).restrictScalars O).comap
            ((latIn O M ⊔ (⨆ x ∈ (Z' : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
              (⨆ x ∈ (Z' : Set X), heckeEig T act x).restrictScalars O).subtype) ≤
      ∑ π ∈ Z', (heckeMult T act π : ℚ) *
        (lenUnit (O := O) l (O ⧸ ccAt T Z π) + padicValInt l A) := by
  by_cases he : (Module.length O (O ⧸ Ideal.span {(l : O)})).toNat = 0
  · simp only [lenUnit, he, Nat.cast_zero, div_zero, zero_add]
    exact Finset.sum_nonneg fun π _ => by positivity
  have heO : Module.length O (O ⧸ Ideal.span {(l : O)}) = addVal O (l : O) :=
    IdempotentNormalFormsLenFacts.length_quot_span _
  obtain ⟨e, hee⟩ : ∃ e : ℕ, addVal O (l : O) = (e : ℕ∞) := by
    rw [heO] at he
    exact ⟨(addVal O (l : O)).toNat, (ENat.natCast_toNat (fun h => he (by rw [h]; rfl))).symm⟩
  have he0 : e ≠ 0 := by
    rw [heO, hee] at he
    simpa using he
  have hlu : ¬ IsUnit (l : O) := by
    intro h
    rw [addVal_eq_zero_iff.mpr h] at hee
    exact he0 (by exact_mod_cast hee.symm)
  have hcore := etaBound O X T hsep (TensorProduct O (FractionRing O) M) (actK T act).toRingHom
    (eigSpan T act hsep) (latIn O M) fg_latIn span_latIn
    (fun f v hv => baseChange_latIn (act f) v hv) Z Z' hZ' (α.baseChange (FractionRing O)) A
    (baseChange_latIn α)
    (fun f => by
      show Module.End.baseChangeHom O (FractionRing O) M α *
          Module.End.baseChangeHom O (FractionRing O) M (act f) =
        Module.End.baseChangeHom O (FractionRing O) M (act f) *
          Module.End.baseChangeHom O (FractionRing O) M α
      rw [← map_mul, ← map_mul, hcomm f])
    (fun x hx v hv => h1 x hx v (by rw [heckeEig_eq]; exact hv))
    (fun x hx hx' v hv => h0 x hx hx' v (by rw [heckeEig_eq]; exact hv))
    (fun x => vcc T (Z : Set X) x) (fun x _ => le_rfl)
  have hlen := (len_le T act hsep (latIn O M) Z').trans hcore
  have hE : heckeEig T act = Vx T (actK T act).toRingHom := funext (heckeEig_eq T act)
  simp only [heckeMult, lenUnit, length_ccAt, heO, hee, ENat.toNat_natCast]
  rw [hE]
  rw [addVal_int l hlu A hA, hee] at hlen
  have hfin : ∀ π ∈ Z', vcc T (Z : Set X) π = ((vcc T (Z : Set X) π).toNat : ℕ∞) :=
    fun π hπ => (ENat.natCast_toNat (vcc_ne_top T hsep Z π (hZ' hπ))).symm
  have hsum : ∑ x ∈ Z', (Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) *
        (vcc T (Z : Set X) x + (padicValInt l A : ℕ∞) * (e : ℕ∞)) =
      ((∑ x ∈ Z', Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) *
        ((vcc T (Z : Set X) x).toNat + padicValInt l A * e) : ℕ) : ℕ∞) := by
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← hfin x hx]
  rw [hsum] at hlen
  have hnat := ENat.toNat_le_of_le_natCast hlen
  have heq : (0 : ℚ) < e := by exact_mod_cast Nat.pos_of_ne_zero he0
  rw [div_le_iff₀ heq, Finset.sum_mul]
  refine (Nat.cast_le (α := ℚ).mpr hnat).trans (le_of_eq ?_)
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  field_simp

end Main

theorem hecke_length_bound_localised {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
    (Z' : Finset (N.X i)) (hZ' : Z' ⊆ N.Z i) (α : Module.End (N.O i) (N.Mt i)) (A : ℤ) (hA : A ≠ 0)
    (hcomm : ∀ f : N.T i, α * N.act i f = N.act i f * α)
    (h1 : ∀ x ∈ Z', ∀ u ∈ heckeEig (N.T i) (N.act i) x,
      α.baseChange (Formalism.MainNotions.N.KK N i) u = (A : Formalism.MainNotions.N.KK N i) • u)
    (h0 : ∀ x ∈ N.Z i, x ∉ Z' → ∀ u ∈ heckeEig (N.T i) (N.act i) x,
      α.baseChange (Formalism.MainNotions.N.KK N i) u = 0) :
    lenUnit (O := N.O i) (N.l i)
        (↥(Formalism.MainNotions.N.MtUp N i Z') ⧸ (Formalism.MainNotions.N.MtLow N i Z').comap (Formalism.MainNotions.N.MtUp N i Z').subtype) ≤
      ∑ π ∈ Z', (N.mult i π : ℚ) * (N.vcc i π + padicValInt (N.l i) A) := by
  have := N.T_local i
  exact hecke_length_bound (N.T i) (N.act i) (N.l i) (N.T_sep i) (N.Z i) Z' hZ' α A hA hcomm h1 h0

theorem EigSpan_holds {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) :
    N.EigSpan := by
  intro i
  have h := eigSpan (N.T i) (N.act i) (N.T_sep i)
  have hE : heckeEig (N.T i) (N.act i) = Formalism.NG.Vx (N.T i) (actK (N.T i) (N.act i)).toRingHom :=
    funext (heckeEig_eq (N.T i) (N.act i))
  rw [hE]
  exact h

theorem etaLoc_eq {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    N.etaLoc i = lenUnit (O := N.O i) (N.l i)
      (↥(Formalism.MainNotions.N.MtUp N i (N.Zgood i)) ⧸
        (Formalism.MainNotions.N.MtLow N i (N.Zgood i)).comap (Formalism.MainNotions.N.MtUp N i (N.Zgood i)).subtype) := by
  unfold Formalism.BasicNotions.NData.etaLoc Formalism.BasicNotions.NData.MtUp Formalism.BasicNotions.NData.MtLow Formalism.MainNotions.N.MtUp Formalism.MainNotions.N.MtLow
  rw [inf_comm (Submodule.restrictScalars (N.O i)
    (N.eigSum i ((N.Zgood i : Finset (N.X i)) : Set (N.X i))))]
  rfl

section Unit

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem l_ne_zero : ((N.l i : ℕ) : N.O i) ≠ 0 := by
  intro h
  have h1 : ((N.l i : ℕ) : what₂.LL) ≠ 0 := by
    intro h0
    have h2 := congrArg what₂.embLL h0
    rw [map_natCast, map_zero] at h2
    exact (N.lPrime i).out.ne_zero (by exact_mod_cast h2)
  have h3 : N.embK i ((N.l i : ℕ) : what₂.LL) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap (N.O i) (FractionRing (N.O i))), h, map_zero]
  exact h1 ((map_eq_zero (N.embK i)).mp h3)

theorem l_not_unit : ¬ IsUnit ((N.l i : ℕ) : N.O i) := by
  intro hu
  have hker : RingHom.ker (algebraMap ℤ_[N.l i] (N.O i)) ≤ IsLocalRing.maximalIdeal ℤ_[N.l i] :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := N.O i)
    (IsLocalRing.maximalIdeal ℤ_[N.l i]) hker
  have hl : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  rw [← hQc, Ideal.mem_comap, map_natCast] at hl
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hl hu)

theorem exists_eO : ∃ e : ℕ, e ≠ 0 ∧ addVal (N.O i) ((N.l i : ℕ) : N.O i) = (e : ℕ∞) := by
  have h0 := l_ne_zero N i
  have h1 := l_not_unit N i
  have htop : addVal (N.O i) ((N.l i : ℕ) : N.O i) ≠ ⊤ := fun h =>
    h0 ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  refine ⟨(addVal (N.O i) ((N.l i : ℕ) : N.O i)).toNat, ?_, (ENat.coe_toNat htop).symm⟩
  intro h
  rcases ENat.toNat_eq_zero.mp h with h | h
  · exact h1 ((IsDiscreteValuationRing.addVal_eq_zero_iff).mp h)
  · exact htop h

theorem lenUnit_span {a : N.O i} {m : ℕ}
    (ha : addVal (N.O i) a = (m : ℕ∞) * addVal (N.O i) ((N.l i : ℕ) : N.O i)) :
    lenUnit (O := N.O i) (N.l i) (N.O i ⧸ Ideal.span {a}) = (m : ℚ) := by
  obtain ⟨e, he0, he⟩ := exists_eO N i
  unfold lenUnit
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, ha, he]
  have h : ((m : ℕ∞) * (e : ℕ∞)).toNat = m * e := by
    rw [← Nat.cast_mul, ENat.toNat_natCast]
  rw [h, ENat.toNat_natCast]
  have : (e : ℚ) ≠ 0 := by exact_mod_cast he0
  push_cast
  field_simp

end Unit

section Del

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem addVal_pow_sub_one (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] (hl0 : (l : O) ≠ 0)
    (hlu : ¬ IsUnit (l : O)) (s₀ : ℕ) (h1 : 1 ≤ s₀) (h2 : l = 2 → 2 ≤ s₀) (u : ℤ_[l]ˣ) (k : ℕ)
    (hk : 0 < k) :
    addVal O ((algebraMap ℤ_[l] O (1 + (l : ℤ_[l]) ^ s₀ * (u : ℤ_[l]))) ^ k - 1) =
      ((s₀ + padicValNat l k : ℕ) : ℕ∞) * addVal O (l : O) := by
  set y : ℤ_[l] := 1 + (l : ℤ_[l]) ^ s₀ * (u : ℤ_[l]) with hy
  set m : ℕ := s₀ + padicValNat l k with hm
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec (m + 1) y)
  set x : ℤ := ((y.appr (m + 1) : ℕ) : ℤ) with hx
  have hyx : y = (x : ℤ_[l]) + (l : ℤ_[l]) ^ (m + 1) * z := by
    have : (x : ℤ_[l]) = ((y.appr (m + 1) : ℕ) : ℤ_[l]) := by rw [hx]; push_cast; rfl
    rw [this, ← hz]
    ring
  have hms : m + 1 = s₀ + (padicValNat l k + 1) := by omega
  have hx1 : ((x - 1 : ℤ) : ℤ_[l]) =
      (l : ℤ_[l]) ^ s₀ * ((u : ℤ_[l]) - (l : ℤ_[l]) ^ (padicValNat l k + 1) * z) := by
    have h : (x : ℤ_[l]) = y - (l : ℤ_[l]) ^ (m + 1) * z := by rw [hyx]; ring
    push_cast
    rw [h, hy, hms, pow_add]
    ring
  have hd1 : (l : ℤ) ^ s₀ ∣ x - 1 := by
    rw [← PadicInt.pow_p_dvd_int_iff, hx1]
    exact Dvd.intro _ rfl
  have hd2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 := by
    rw [← PadicInt.pow_p_dvd_int_iff, hx1, pow_succ]
    intro h
    have hp0 : (l : ℤ_[l]) ^ s₀ ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have h3 := (mul_dvd_mul_iff_left hp0).mp h
    have h4 : (l : ℤ_[l]) ∣ (u : ℤ_[l]) := by
      have h5 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ (padicValNat l k + 1) * z :=
        Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero _)) _
      have := dvd_add h3 h5
      simpa using this
    exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit h4 u.isUnit)
  have hcore := Formalism.NG.character_column_kernel_length_bound l s₀ h1 h2 x hd1 hd2 0 k hk
  rw [pow_zero, Nat.sub_zero] at hcore
  have hne : x ^ k - 1 ≠ 0 := by
    intro h0
    rw [h0, padicValInt.zero] at hcore
    omega
  have hA := addVal_int (O := O) l hlu (x ^ k - 1) hne
  rw [hcore] at hA
  obtain ⟨q, hq⟩ : (algebraMap ℤ_[l] O y - (x : O)) ∣ (algebraMap ℤ_[l] O y) ^ k - (x : O) ^ k :=
    sub_dvd_pow_sub_pow _ _ _
  have hyO : algebraMap ℤ_[l] O y - (x : O) = (l : O) ^ (m + 1) * algebraMap ℤ_[l] O z := by
    rw [hyx, map_add, map_mul, map_pow, map_natCast, map_intCast]
    ring
  have hsplit : (algebraMap ℤ_[l] O y) ^ k - 1 =
      ((x ^ k - 1 : ℤ) : O) + (l : O) ^ (m + 1) * (algebraMap ℤ_[l] O z * q) := by
    have : (algebraMap ℤ_[l] O y) ^ k = (x : O) ^ k + (l : O) ^ (m + 1) * algebraMap ℤ_[l] O z * q := by
      rw [← hyO, ← hq]
      ring
    rw [this]
    push_cast
    ring
  obtain ⟨e, he⟩ : ∃ e : ℕ, addVal O (l : O) = (e : ℕ∞) :=
    ⟨(addVal O (l : O)).toNat, (ENat.natCast_toNat (fun h => hl0 (addVal_eq_top_iff.mp h))).symm⟩
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h] at he
      exact absurd (addVal_eq_zero_iff.mp (by simpa using he)) hlu
    · exact h
  have hlt : addVal O ((x ^ k - 1 : ℤ) : O) <
      addVal O ((l : O) ^ (m + 1) * (algebraMap ℤ_[l] O z * q)) := by
    rw [hA, addVal_mul, addVal_pow, he]
    have h6 : ((m : ℕ) : ℕ∞) * (e : ℕ∞) < (m + 1) • (e : ℕ∞) := by
      rw [nsmul_eq_mul]
      have : m * e < (m + 1) * e := by nlinarith
      exact_mod_cast this
    exact lt_of_lt_of_le h6 le_self_add
  rw [hsplit, AddValuation.map_add_eq_of_lt_left _ hlt, hA]

end Del

end Br

theorem endomorphism_index_bound {D : Formalism.BasicNotions.D7} (i : D.nd.Loc) : EndomorphismIndexBound i := by
  unfold EndomorphismIndexBound
  intro Z' hZ' α A hA hcomm h1 h0
  exact Br.hecke_length_bound_localised D.nd i Z' hZ' α A hA hcomm h1 h0

theorem second_statement (D : Formalism.BasicNotions.D7) : HodgeTateFromSandwich D := by
  unfold HodgeTateFromSandwich
  exact fun i => endomorphism_index_bound i

end Formalism.MainNotions.TruncatedSeriesCountingIdentities
