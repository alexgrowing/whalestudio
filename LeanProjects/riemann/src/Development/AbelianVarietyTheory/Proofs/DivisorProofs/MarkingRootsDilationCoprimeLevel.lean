import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem level_smul_levQ (q : LevQ Dw l) : l.M • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (level_mem l).1 trivial

theorem cSep_smul_levQ (q : LevQ Dw l) : cSep l • q = q := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have e : cSep l • y - y = (cSep l - 1) • y := by rw [sub_smul, one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (cSep_spec l).2 trivial

theorem sub_sepRep (q : LevQ Dw l) (x : Dw.La) (hx : x ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (hq : Submodule.Quotient.mk x = q) : ∃ z : Dw.La, x - cSep l • levRep q = l.M • z := by
  have h1 : x - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
    (Submodule.Quotient.eq _).1 (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)).symm)
  obtain ⟨b1, hb1⟩ := modN_smul l ((mul_comm _ _).trans l.prod) (cSep_spec l).1 h1
  obtain ⟨b2, hb2⟩ := modN_smul l l.prod (cSep_spec l).2 hx
  refine ⟨b1 - b2, ?_⟩
  rw [smul_sub, ← hb1, ← hb2, smul_sub, sub_smul, one_smul]
  abel

end GlobalTheory.DilateLevel

namespace GlobalTheory.DilateLevel

open GlobalTheory.Dict.MarkMove

theorem dilate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (r n : ℕ) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (m : ℤ), IsCoprime m (l.M : ℤ) → (IsMark l L mk → IsMark l L (m • mk)) ∧ ∀ (N : ℕ) (Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E), ((∀ a, mk a ∈ L) → IsRoots l L mk N Y → IsRoots l L (m • mk) N (fun q => Y (m • q))) ∧ ∀ (g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (w : E) (Λ : Lt E n) (v : TF n g) (c : (Fin n → LevQ Dw l) → ℂ), gphi X bas w Λ L v (fun q => c (m • q)) (fun q => Y (m • q)) = gphi X bas w Λ L v c Y := by
  intro E _ _ _ H Dw l r n L mk m hm
  refine hm.elim fun α hβ => hβ.elim fun β hab => ?_
  have hM0 : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hsm : ∀ a, (m • mk) a = m • mk a := fun a => LinearMap.smul_apply _ _ _
  have hbez : ∀ x : Fin r → E, x = α • (m • x) + β • (l.M • x) := fun x => by
    rw [smul_smul, ← natCast_zsmul, smul_smul, ← add_smul, hab, one_smul]
  refine ⟨fun h => ?_, fun N Y => ⟨fun hmem h => ?_, fun g X bas w Λ v c => ?_⟩⟩
  · refine ⟨fun a => by rw [hsm]; exact zsmul_mem (h.mem a) m, fun a ha hu => ?_, fun v hv => ?_⟩
    · refine hu.elim fun u hu' => h.inj a ha ⟨α • u + β • mk a, add_mem (zsmul_mem hu'.1 α) (zsmul_mem (h.mem a) β), ?_⟩
      have e : m • mk a = l.M • u := (hsm a).symm.trans hu'.2
      refine (hbez (mk a)).trans ?_
      rw [e, smul_add, smul_comm α, smul_comm β]
    · have hvL : v ∈ L := Submodule.smul_le_right hv
      refine (h.surj (α • v) (zsmul_mem hv α)).elim fun a1 h1 => h1.elim fun ha1 h2 => h2.elim fun u1 h3 => ?_
      refine ⟨a1, ha1, m • u1 + β • v, add_mem (zsmul_mem h3.1 m) (zsmul_mem hvL β), ?_⟩
      have e : α • v = mk a1 + l.M • u1 := h3.2
      refine (hbez v).trans ?_
      rw [smul_comm α m, e, hsm, smul_add, smul_add, smul_comm m, smul_comm β]
      abel
  · intro q b
    have h0 := h (m • q) b
    refine ⟨?_, h0.2⟩
    refine h0.1.elim fun a0 k => k.elim fun ha0 k2 => ?_
    have hq0 : Submodule.Quotient.mk a0 = m • q b := k2.1
    have hY0 := k2.2
    set a' : Dw.La := cSep l • levRep (q b) with ha'
    have ha'm : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul (cSep_spec l).1 trivial
    have hcls : (Submodule.Quotient.mk a' : LevQ Dw l) = q b := by
      have hr : (Submodule.Quotient.mk (levRep (q b)) : LevQ Dw l) = q b :=
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))
      rw [ha', Submodule.Quotient.mk_smul, hr, cSep_smul_levQ]
    refine ⟨a', ha'm, hcls, ?_⟩
    have hm' : (Submodule.Quotient.mk (m • a') : LevQ Dw l) = m • q b := by
      rw [Submodule.Quotient.mk_smul, hcls]
    refine (sub_sepRep (m • q b) a0 ha0 hq0).elim fun z1 hz1 => ?_
    refine (sub_sepRep (m • q b) (m • a') (zsmul_mem ha'm m) hm').elim fun z2 hz2 => ?_
    have hd : a0 - m • a' = l.M • (z1 - z2) := by
      rw [smul_sub, ← hz1, ← hz2]; abel
    have key : ((l.M : E)⁻¹) • (mk a0 - (m • mk) a') = mk (z1 - z2) := by
      rw [hsm, ← map_zsmul mk, ← map_sub, hd, map_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM0]
    have := add_mem hY0 (hmem (z1 - z2))
    rw [← key] at this
    convert this using 1
    rw [smul_sub]
    abel
  · have hk : ∀ q : Fin n → LevQ Dw l, ((l.M : ℤ)) • q = 0 := fun q => funext fun b => by
      rw [Pi.smul_apply, natCast_zsmul, level_smul_levQ]; rfl
    have hinv : ∀ q : Fin n → LevQ Dw l, α • m • q = q := fun q => by
      rw [smul_smul, show α * m = 1 - β * l.M by linear_combination hab, sub_smul, one_smul, mul_smul, hk,
        smul_zero, sub_zero]
    let e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l) :=
      { toFun := fun q => m • q
        invFun := fun q => α • q
        left_inv := fun q => hinv q
        right_inv := fun q => by
          change m • α • q = q
          rw [smul_comm]; exact hinv q }
    exact finsum_comp_equiv e (f := fun q => c q • heisG X bas (Y q) (projA X bas w (tens Λ L) v))

end GlobalTheory.DilateLevel
