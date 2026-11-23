import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocInd
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondPreservesRationalFormZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified

noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField Classical IsDedekindDomain

variable {D : D7} {u : D.what₂.Word}

def ValuesIntegralAllBases (T : Forms0 D u) (w : D.what₂.places.Pl) (φ : Fn D u 0) : Prop :=
  ∀ (c : (D.mem u).C.cls 0) (B : GL (Fin (D.R.N 0)) D.host.E),
    IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
    ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ z, φ c z =
      fnOf _ (shiftOf (lamT u 0)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P (T.val0.eY z)

def ValuesIntegralNeighbourBases (T : Forms0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) (φ : Fn D u 0) : Prop :=
  ∀ (c : (D.mem u).C.cls 0) (B B' : GL (Fin (D.R.N 0)) D.host.E),
    IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
    IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) B' →
    ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ z, φ c z =
      fnOf _ (shiftOf (lamT u 0))
        (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
          else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ) P (T.val0.eY z)

def UpValInt0 (T : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v (x : Vl D u 0),
    ValuesIntegralNeighbourBases T w v ((D.fm u).emb 0 x) → ValuesIntegralAllBases T w (Uop D u 0 v ((D.fm u).emb 0 x))

def DnValInt0 (T : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v (x : Vl D u 0),
    ValuesIntegralAllBases T w ((D.fm u).emb 0 x) → ValuesIntegralNeighbourBases T w v (Dop D u 0 v ((D.fm u).emb 0 x))

theorem mem_Bw_iff (T : Forms0 D u) {w : D.what₂.places.Pl} (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (x : Vl D u 0) : x ∈ (D.fm u).Bw 0 w v ↔ ValuesIntegralNeighbourBases T w v ((D.fm u).emb 0 x) :=
  T.bw0 w hw hs v x

theorem mem_S_of_val (T : Forms0 D u) {w : D.what₂.places.Pl} (hw : OverT D u w) (y : Vl D u 0)
    (hy : ValuesIntegralAllBases T w ((D.fm u).emb 0 y)) : y ∈ (D.fm u).S 0 w := by
  show y ∈ locW D.what₂.places w ((D.fm u).lat 0).L
  rw [D.mem_locW_iff]
  obtain ⟨-, -, hsp⟩ := (D.fm u).lat_good 0
  obtain ⟨d, hd, hdy⟩ := Formalism.L2.DIV.lc_exists_smul_mem ((D.fm u).lat 0).L (x := y) (by rw [hsp]; trivial)
  obtain ⟨t, ht, htw⟩ := Formalism.L2.DIV.lc_primeTo d hd (D.plEq w)
  refine ⟨t, ht, ?_⟩
  refine (T.val0.lat _).2 fun w' c B hB => ?_
  by_cases hw' : w' = w
  · subst hw'
    have hB' : IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B := by
      rw [LocalLatticeBases.bwG_Ld_coe, ← hw]
      exact hB
    obtain ⟨Q, hQ, hyQ⟩ := hy c B hB'
    refine ⟨_, LocalLatticeBases.bwG_intSpan_smul D w' _ _ (LocalLatticeBases.bwG_int_mem D w' t) hQ, fun z => ?_⟩
    rw [← algebraMap_smul D.what₂.LL t y, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hyQ z,
      LinearMap.map_smul]
    rfl
  · have hne : D.plEq w' ≠ D.plEq w := fun h => hw' (D.plEq.injective h)
    obtain ⟨r, hr, k, hk⟩ := htw _ hne
    obtain ⟨P, hP, hdP⟩ := (T.val0.lat _).1 hdy w' c B hB
    have hr0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL r ≠ 0 := by
      intro h
      apply hr
      have : r = 0 := FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [h, map_zero])
      rw [this]
      exact zero_mem _
    have e : t • y = ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ * algebraMap (𝓞 D.what₂.LL) D.what₂.LL k) • (d • y) := by
      rw [← algebraMap_smul D.what₂.LL t y, ← algebraMap_smul D.what₂.LL d y, smul_smul]
      congr 1
      have hk' := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) hk
      rw [map_mul, map_mul] at hk'
      field_simp
      rw [mul_comm, hk', mul_comm]
    refine ⟨_, LocalLatticeBases.bwG_intSpan_smul D w' _ _ (mul_mem (LocalLatticeBases.bwG_inv_mem D w' hr) (LocalLatticeBases.bwG_int_mem D w' k)) hP, fun z => ?_⟩
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hdP z, LinearMap.map_smul]
    rfl

theorem val_of_mem_S (T : Forms0 D u) {w : D.what₂.places.Pl} (hw : OverT D u w) (x : Vl D u 0)
    (hx : x ∈ (D.fm u).S 0 w) : ValuesIntegralAllBases T w ((D.fm u).emb 0 x) := by
  intro c B hB
  obtain ⟨t, ht, htx⟩ := (D.mem_locW_iff w _ x).1 hx
  have hB2 : IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B := by
    rw [show D.what₂.places.resChar w = (D.mem u).A.T from hw, ← LocalLatticeBases.bwG_Ld_coe]
    exact hB
  obtain ⟨P, hP, hxP⟩ := (T.val0.lat (t • x)).1 htx w c B hB2
  have ht0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL t ≠ 0 := by
    intro h
    apply ht
    have : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [h, map_zero])
    rw [this]
    exact zero_mem _
  refine ⟨D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL t)⁻¹ • P,
    LocalLatticeBases.bwG_intSpan_smul D w _ _ (LocalLatticeBases.bwG_inv_mem D w ht) hP, fun z => ?_⟩
  have hz := hxP z
  rw [← algebraMap_smul D.what₂.LL t x, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply] at hz
  rw [LinearMap.map_smul, Pi.smul_apply, ← hz, smul_eq_mul, smul_eq_mul, ← mul_assoc, map_inv₀,
    inv_mul_cancel₀ ((map_ne_zero D.what₂.embLL).2 ht0), one_mul]

theorem integrality_of_rationality_local (T : Forms0 D u) (hR : HeckeRationalLevelZero D u) (hU : UpValInt0 T) (hD : DnValInt0 T) : HeckeIntegralLevelZero D u := by
  intro w hw hs v
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := (hR v x).1
    refine ⟨y, mem_S_of_val T hw y ?_, hy⟩
    rw [hy]
    exact hU w hw hs v x ((mem_Bw_iff T hw hs v x).1 hx)
  · obtain ⟨y, hy⟩ := (hR v x).2
    refine ⟨y, (mem_Bw_iff T hw hs v y).2 ?_, hy⟩
    rw [hy]
    exact hD w hw hs v x (val_of_mem_S T hw x hx)

theorem chiFin0_sym {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (h : Formalism.MainNotions.RT.ChiFin0 T) : LocalLatticeBases.ChiFin0 T.to0 := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, fun i hi h0 x => ?_⟩
  subst h0
  exact h x

theorem integrality_at_forms_of_values
    (hR : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → HeckeRationalLevelZero D u)
    (hU : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → UpValInt0 T)
    (hD : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → DnValInt0 T)
    (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u := by
  rintro ⟨Ch, chOf, T, hC⟩ hA hS
  have hC0 := chiFin0_sym T hC
  exact integrality_of_rationality_local T.to0 (hR D u _ hC0 hA hS) (hU D u _ hC0 hA hS) (hD D u _ hC0 hA hS)

end PI.UnitaryGroupMassFormula.IAT

end
