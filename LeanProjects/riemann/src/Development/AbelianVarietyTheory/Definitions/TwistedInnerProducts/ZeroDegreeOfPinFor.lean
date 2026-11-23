import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportPin.Model

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S)

set_option synthInstance.maxHeartbeats 400000 in

def PinFor (hk : ∀ i j b, ℕ → PlE D.host → Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) : Prop :=
  ∀ (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)),
    Reads Rl cG S Y hL → ∃ u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ,
      ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
        Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
        Y.eF i j b h1 h2 (hk i j b k P x) =
          (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
            hkFR S i j b (hL j) (hs j h1 h2) k P (Y.eF i j b h1 h2 x)

theorem heckePin_iff : HeckePin Rl cG S Y ↔ PinFor Rl cG S Y D.nexp.hkF := Iff.rfl

def Covered : Prop :=
  ∀ (i : D.ntw.Tw) (P : PlE D.host), P ∉ D.ntw.S0 i → Formalism.BasicNotions.IsSplitPl D.host P →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E))

theorem covered_of_allPlaces (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hA : Rl.AllPlaces) : Covered Rl := by
  intro i P hP hs
  have hA' : Rl.Sb = Rl.Pg := hA
  have key : ∀ Q ∈ Rl.Sb, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
    intro Q hQ
    rw [hA'] at hQ
    obtain ⟨k, hk⟩ := (hL.Pg Q).1 hQ
    have h1 := Rl.C.P.pb_over k
    have h2 : Q.under (𝓞 D.host.K) = Rl.C.P.pb k := hk
    rw [← h2] at h1
    have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal := h1
    exact ⟨k, by rwa [map_natCast] at h3⟩
  refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hs, fun h => ?_, fun Q hQ h => ?_⟩
  · obtain ⟨k, hk⟩ := key P h
    exact hP (D.ntw.placesOver_subset_exceptional i k hk)
  · obtain ⟨k, hk⟩ := key Q hQ
    rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hk
    exact hP (D.ntw.placesOver_subset_exceptional i k hk)

theorem j_injective (hU : Rl.toRealDat.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Function.Injective ((Rl.FW i).j σ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have := (hU i σ).1 1 (fun _ => x) (by rw [linearIndependent_unique_iff]; exact h0)
  rw [linearIndependent_unique_iff] at this
  exact this hx

theorem reads_unique (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hU : Rl.toRealDat.LUnif)
    (hW : Rl.toRealDat.models_HW) {f f' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (h : Reads Rl cG S Y f) (h' : Reads Rl cG S Y f') (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host)
    (hs : Formalism.BasicNotions.IsSplitPl D.host P) (ho : Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (hk : k ≤ D.R.r) : f j k P = f' j k P := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  let i : Fin D.R.m := ⟨n, h2⟩
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hL hF i ho hk
  ext x
  have e := (h i k P hs ho hk α Rc ha hR x).trans (h' i k P hs ho hk α Rc ha hR x).symm
  exact (Y.fi i).e.injective (j_injective Rl hU i _ ((hW i _).1 e))

theorem hkFR_congr (i : D.ntw.Tw) (j : ℕ) (b : Bool) {f f' : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hs : HeckeStabR S j f) (hs' : HeckeStabR S j f') (k : ℕ) (P : PlE D.host) (h : f k P = f' k P) :
    hkFR S i j b f hs k P = hkFR S i j b f' hs' k P := by
  unfold hkFR
  congr 1
  ext x
  exact congrArg (fun t : Module.End D.what₂.LL (S.WL j) => t x) h

set_option synthInstance.maxHeartbeats 400000 in

def baseChangeOps (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)) :
    ∀ i j b, ℕ → PlE D.host → Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) := fun i j b k P =>
  if h : 1 ≤ j ∧ j ≤ D.R.m then (Y.eF i j b h.1 h.2).symm.conj (hkFR S i j b (f j) (hs j h.1 h.2) k P) else 0

set_option synthInstance.maxHeartbeats 400000 in

theorem pinFor_baseChange (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hU : Rl.toRealDat.LUnif)
    (hW : Rl.toRealDat.models_HW) (hC : Covered Rl) (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)) (hf : Reads Rl cG S Y f) :
    PinFor Rl cG S Y (baseChangeOps Rl cG S Y f hs) := by
  intro f' hs' hf'
  refine ⟨fun _ _ _ => 1, fun i j b h1 h2 k P x hP hsp hk => ?_⟩
  have e := hkFR_congr S i j b (hs j h1 h2) (hs' j h1 h2) k P
    (reads_unique Rl cG S Y hL hF hU hW hf hf' j h1 h2 k P hsp (hC i P hP hsp) hk)
  rw [← e, baseChangeOps, dif_pos ⟨h1, h2⟩, LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_symm, Units.val_one, map_one, one_pow, one_smul]

theorem exists_pinFor (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hU : Rl.toRealDat.LUnif)
    (hW : Rl.toRealDat.models_HW) (hA : Rl.AllPlaces) : ∃ hk, PinFor Rl cG S Y hk := by
  by_cases h : ∃ (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (_ : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)), Reads Rl cG S Y f
  · obtain ⟨f, hs, hf⟩ := h
    exact ⟨_, pinFor_baseChange Rl cG S Y hL hF hU hW (covered_of_allPlaces Rl hL hA) f hs hf⟩
  · exact ⟨D.nexp.hkF, fun f hs hf => absurd ⟨f, hs, hf⟩ h⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem row_of_pin (hp : HeckePin Rl cG S Y) (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)) (hf : Reads Rl cG S Y f)
    (eW : ∀ j, Module.End D.what₂.LL (S.WL j)) :
    ∃ H : NExpRealH Rl cG S Y, H.hL = f ∧ NExpHeckeRowX Rl cG S Y H eW ∧
      ∀ i b P, ∃ u : (D.ntw.O i)ˣ, H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
  obtain ⟨u, hu⟩ := hp f hs hf
  refine ⟨⟨f, hs, fun i b k P => (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k,
    fun _ _ _ => pow_zero _, fun i b P => ?_, fun i b k P => by rw [pow_one], hu⟩, rfl,
    ⟨fun i k P h1 h2 _ _ hk α R ha hR x _ => hf i k P h1 h2 hk α R ha hR x⟩, fun i b P => ⟨u i b P, pow_one _⟩⟩
  exact ((u i b P).isUnit.map _).pow 1

set_option synthInstance.maxHeartbeats 400000 in

theorem hkFR_of_smul (i : D.ntw.Tw) (j : ℕ) (b : Bool) {f : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hs : HeckeStabR S j f) (k : ℕ) (P : PlE D.host) :
    (f k P = 0 → hkFR S i j b f hs k P = 0) ∧ (f k P = 1 → hkFR S i j b f hs k P = 1) := by
  constructor
  · intro h
    unfold hkFR
    have : ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) (fun x hx => hs k P x hx) = 0 := by
      ext x
      exact congrArg (fun t : Module.End D.what₂.LL (S.WL j) => t x) h
    rw [this]
    exact map_zero (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j))
  · intro h
    unfold hkFR
    have : ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) (fun x hx => hs k P x hx) = 1 := by
      ext x
      exact congrArg (fun t : Module.End D.what₂.LL (S.WL j) => t x) h
    rw [this]
    exact map_one (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j))

set_option synthInstance.maxHeartbeats 400000 in

theorem not_pinFor (hk : ∀ i j b, ℕ → PlE D.host → Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))
    (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)) (hf : Reads Rl cG S Y f)
    (i : D.ntw.Tw) (P : PlE D.host) (hP : P ∉ D.ntw.S0 i) (hsp : Formalism.BasicNotions.IsSplitPl D.host P)
    (ho : ¬ Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) (x : D.nexp.Fm i j b) (hx : x ≠ 0) :
    ¬ PinFor Rl cG S Y hk := by
  classical
  intro hp
  have main : ∀ c : ∀ j, Module.End D.what₂.LL (S.WL j), (∀ j x, x ∈ (S.A j).WK → c j x ∈ (S.A j).WK) →
      ∃ (g : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hg : HeckeStabR S j g), g 0 P = c j ∧
        Y.eF i j b h1 h2 (hk i j b 0 P x) = hkFR S i j b g hg 0 P (Y.eF i j b h1 h2 x) := by
    intro c hc
    let g : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j) := fun j k Q => if Q = P then c j else f j k Q
    have hg : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (g j) := by
      intro j h1 h2 k Q y hy
      by_cases hQ : Q = P
      · simp only [g, if_pos hQ]; exact hc j y hy
      · simp only [g, if_neg hQ]; exact hs j h1 h2 k Q y hy
    have hr : Reads Rl cG S Y g := by
      intro i' k Q q1 q2 q3 α R ha hR y
      have hQ : Q ≠ P := fun e => ho (e ▸ q2)
      simp only [g, if_neg hQ]
      exact hf i' k Q q1 q2 q3 α R ha hR y
    obtain ⟨u, hu⟩ := hp g hg hr
    refine ⟨g j, hg j h1 h2, if_pos rfl, ?_⟩
    rw [hu i j b h1 h2 0 P x hP hsp (Nat.zero_le _), pow_zero, one_smul]
  obtain ⟨g0, hg0, e0, a0⟩ := main (fun _ => 0) (fun j x _ => (S.A j).WK.zero_mem)
  obtain ⟨g1, hg1, e1, a1⟩ := main (fun _ => 1) (fun j x hx => hx)
  rw [(hkFR_of_smul S i j b hg0 0 P).1 e0] at a0
  rw [(hkFR_of_smul S i j b hg1 0 P).2 e1, a0] at a1
  exact hx ((Y.eF i j b h1 h2).map_eq_zero_iff.1 a1.symm)

theorem exists_reads
    (h : ∀ (i : Fin D.R.m) (P : PlE D.host), Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
      ∀ k : ℕ, k ≤ D.R.r → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHeckeAt Rl.toRealDat i P k) :
    ∃ (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
      (_ : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)), Reads Rl cG S Y f := by
  have h' : ∀ (i : Fin D.R.m) (k : ℕ) (P : PlE D.host), ∃ t : Module.End D.what₂.LL (Fin (Rl.nW i) → D.what₂.LL),
      (∀ x ∈ (Rl.FW i).WK, t x ∈ (Rl.FW i).WK) ∧
      (Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
        ∀ Rc, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.IsCosetSys Rl.toRealDat i P k Rc → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.ReadAs Rl.toRealDat i P k Rc t) := by
    intro i k P
    by_cases hc : Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧ k ≤ D.R.r
    · obtain ⟨t, t1, t2⟩ := h i P hc.1 k hc.2
      exact ⟨t, t2, fun _ _ => t1⟩
    · exact ⟨1, fun x hx => hx, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose t t1 t2 using h'
  obtain ⟨f, hf⟩ := GlobalTheory.HeckeTieCompare.exists_family Rl.toRealDat (WL := S.WL) (fun i => (Y.fi i).e) t
  have e : ∀ (i : Fin D.R.m) k P x, (Y.fi i).e (f ((i : ℕ) + 1) k P x) = t i k P ((Y.fi i).e x) := fun i k P x => by
    rw [← hf i k P, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  refine ⟨f, fun j h1 h2 k P x hx => ?_, fun i k P _ ho hk α R ha hR x => ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    let i : Fin D.R.m := ⟨n, h2⟩
    refine ((Y.fi i).wk _).2 ?_
    rw [e i]
    exact t1 i k P _ (((Y.fi i).wk _).1 hx)
  · rw [e, GlobalTheory.HeckeTieCompare.scalar_eq Rl.toRealDat]
    exact t2 i k P ho hk R ⟨α, ha, hR⟩ _

set_option synthInstance.maxHeartbeats 400000 in

theorem zero_degree_of_pinFor (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) (hC : Covered Rl)
    (hk : ∀ i j b, ℕ → PlE D.host → Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (hp : PinFor Rl cG S Y hk)
    (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j)) (hf : Reads Rl cG S Y f)
    (i : D.ntw.Tw) (P : PlE D.host) (hP : P ∉ D.ntw.S0 i) (hsp : Formalism.BasicNotions.IsSplitPl D.host P)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) (x : D.nexp.Fm i j b) : hk i j b 0 P x = x := by
  have ho := hC i P hP hsp
  have e1 : f j 0 P = 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    let i' : Fin D.R.m := ⟨n, h2⟩
    obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ho.1
    obtain ⟨ϖ, p1, p2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
    have hd : Bridge.IsDC (levG (Wc D i') (Rl.βW i') (Rl.datWp i' Rl.triv)) 1 {1} := by
      refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
      rintro g ⟨k₁, k₂, rfl⟩
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩
      simpa using mul_mem k₁.2 k₂.2
    ext y
    have q := hf i' 0 P hsp ho (Nat.zero_le _) 1 {1} ⟨e, ϖ, he, p1, p2, GlobalTheory.HeckeParts.isHeckeElt_one _ he.1 ϖ⟩ hd y
    have q' := GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_id Rl.toRealDat i' P ((Y.fi i').e y)
    rw [GlobalTheory.HeckeTieCompare.scalar_eq Rl.toRealDat] at q
    exact (Y.fi i').e.injective (j_injective Rl hU i' _ ((hW i' _).1 (q.trans q'.symm)))
  obtain ⟨u, hu⟩ := hp f hs hf
  have := hu i j b h1 h2 0 P x hP hsp (Nat.zero_le _)
  rw [pow_zero, one_smul, (hkFR_of_smul S i j b (hs j h1 h2) 0 P).2 e1] at this
  exact (Y.eF i j b h1 h2).injective this

end GlobalTheory.ExportPin.Model
