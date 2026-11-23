import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmulMorPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.HomP

open Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
  {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n}
  {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)

def muEta (T : (L'.QB M).FullSubcategory) :
    (kS L.γB N.q (L.QB N)).G.obj (((h.nmW u hu).smor _ _ (h.nmW_mem u hu)).G.obj T) ⟶
      (smS (Model.genMap u hu) (Model.genMap_q u hu)).G.obj ((kS L'.γB M.q (L'.QB M)).G.obj T) :=
  nlHom (γ := dividedPowersBot K) (κ := Ideal.Quotient.mk ⊥) (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (h.oB r))
    (DPMorphism.id T.obj.δ).isDPMorphism fun e => (spec_id _ e _).trans (by
      change (pt T.obj ≫ Model.genMap u hu) ≫ 𝟙 _ = (pt T.obj ≫ 𝟙 _) ≫ Model.genMap u hu
      rw [Category.comp_id, Category.comp_id])

theorem mu_sq (a r j : ℕ) (y : Hdg N.q a j) :
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y) :=
  genB (kS L.γB N.q (L.QB N)) ((h.nmW u hu).smor _ _ (h.nmW_mem u hu)) (smS (Model.genMap u hu) (Model.genMap_q u hu))
    (kS L'.γB M.q (L'.QB M)) (L.tB ^ (r - a)) (h.cB ^ (r - a)) (L'.tB ^ (r - a)) (fun k => (h.oB k).symm)
    (by rw [map_pow h.sB, h.t, mul_pow]) ⟨muEta h u hu, fun T T' f => hom_ext rfl⟩ (fun _ _ => rfl) _ _ _ _ _ _ _ _ j y

def nmA : NMor L.γ N.p (κA (OK l K) L.I) L'.γ M.p (κA (OK l K) L'.I) h.sA where
  hI := h.dpA
  u := u
  g := RingHom.id _
  hu := by simpa using hu
  hκ a r e := by
    have h1 := h.dpA.1 (Ideal.mem_map_of_mem h.sA (Ideal.Quotient.eq.1 e))
    rw [map_sub, h.oA] at h1
    exact Ideal.Quotient.eq.2 h1

theorem nmA_mem (T : Thick (nlFun L'.γ 0 M.X M.p (κA (OK l K) L'.I))) (hT : L'.QA M T) : L.QA N (((nmA h u hu).mor 0).obj T) :=
  ⟨⟨le_bot_iff.1 (le_trans (T.pdPow_anti h.le) hT.1.1.le), hT.1.2⟩, ⊤, rfl, le_rfl⟩

def smA : SMor (sP (L.QA N)) (sP (L'.QA M)) h.sA := (nmA h u hu).smor _ _ (nmA_mem h u hu)

def mZ (r : ℕ) : CH.Mor (sq (sFil (L.QA N) r) (sFil (L.QA N) ((r : ℤ) + 1))) (sq (sFil (L'.QA M) r) (sFil (L'.QA M) ((r : ℤ) + 1))) h.sA :=
  (smA h u hu).sq (fun _ _ hx => hx) fun _ _ hx => hx

def mZn (r n : ℕ) : CH.Mor (sq (stdI (L.QA N) (some (r : ℤ)) ((l : L.A) ^ n)) (stdI (L.QA N) (some ((r : ℤ) + 1)) ((l : L.A) ^ n)))
    (sq (stdI (L'.QA M) (some (r : ℤ)) ((l : L'.A) ^ n)) (stdI (L'.QA M) (some ((r : ℤ) + 1)) ((l : L'.A) ^ n))) h.sA :=
  (smA h u hu).sq (std_le (nmA h u hu) (nmA_mem h u hu) _) (std_le (nmA h u hu) (nmA_mem h u hu) _)

theorem red_sq (r n j : ℕ) (z : HG (L.QA N) r j) :
    redG' (L'.QA M) ((l : L'.A) ^ n) r j ((mZ h u hu r).pull j z) = (mZn h u hu r n).pull j (redG' (L.QA N) ((l : L.A) ^ n) r j z) :=
  genC (smA h u hu) _ _ _ _ _ _ _ _ j z

def bEta (T : (L'.QB M).FullSubcategory) :
    (smA h u hu).G.obj (((L'.nmB M).smor _ _ (L'.nmB_mem M)).G.obj T) ⟶
      ((L.nmB N).smor _ _ (L.nmB_mem N)).G.obj (((h.nmW u hu).smor _ _ (h.nmW_mem u hu)).G.obj T) :=
  ObjectProperty.homMk (nlHom (γ := L.γ) (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (h.ι r).symm)
    (DPMorphism.id T.obj.δ).isDPMorphism fun e => (spec_id _ e _).trans (by
      change (pt T.obj ≫ pullback.fst _ _) ≫ u = (pt T.obj ≫ Model.genMap u hu) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, Model.genMap, pullback.lift_fst]))

theorem b_sq (r j : ℕ) (z : HG (L.QA N) r j) :
    L'.bG M r j ((mZ h u hu r).pull j z) = h.fW u hu r j (L.bG N r j z) :=
  genA (smA h u hu) ((L'.nmB M).smor _ _ (L'.nmB_mem M)) ((L.nmB N).smor _ _ (L.nmB_mem N)) ((h.nmW u hu).smor _ _ (h.nmW_mem u hu))
    h.ι ⟨bEta h u hu, fun T T' f => ObjectProperty.hom_ext _ (hom_ext rfl)⟩ (fun _ _ => rfl) _ _ _ _ _ _ _ _ j z

variable {n : ℕ} (mm : GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n))
  (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), (mm.pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u)

theorem d_comm (x : Y.R n) (a : L.A) (e : (L.d n).ρ x = Ideal.Quotient.mk _ a) : (L'.d n).ρ (sn n x) = Ideal.Quotient.mk _ (h.sA a) := by
  obtain ⟨b, rfl⟩ := Y.c_surj n x
  rw [L.d_lam] at e
  rw [h.cris, L'.d_lam, ← h.lam]
  exact congrArg (lnMap h.sA l (le_refl n)) e

include hpt in
theorem r_sq (r j : ℕ) (x : CH.H (Y.SS N r n).fn j) :
    (mZn h u hu r n).pull j ((L.rS N r n).pull j x) = (L'.rS M r n).pull j ((pdOm mm sΛ (h.cris n) r).pull j x) :=
  genD (nmA h u hu) (nmA_mem h u hu) (L.d n) (L'.d n) (d_comm h) mm hpt (Y.c n) L.lam L'.lam (L.d_lam n) (L'.d_lam n) sΛ (h.cris n)
    (fun a => (h.lam a).symm) r j x

end CrystallineSemistableComparison.HT.HomP

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem homMu : HomMu l K := fun h _ _ u hu a r j y => HomP.mu_sq h u hu a r j y

theorem HomP.step {A A' : Type} [CommRing A] [CommRing A'] {s : A →+* A'} {P P' : Type 1} [AddCommGroup P] [Module A P]
    [AddCommGroup P'] [Module A' P'] (f : P →ₛₗ[s] P') (l e : ℕ) {a b : P} {a' b' : P'} (h : a = (l : A) ^ e • b) (ha : a' = f a)
    (hb : f b = b') : a' = (l : A') ^ e • b' := by
  rw [ha, h, LinearMap.map_smulₛₗ, map_pow, map_natCast, hb]

theorem homRho : HomRho l K := fun h _ _ u hu mm hpt r j x w hw => hw.elim fun e he => he.elim fun z hz =>
  ⟨e, (HomP.mZ h u hu r).pull j z,
    fun n => HomP.step ((HomP.mZn h u hu r n).pull j) l e (hz.1 n) (HomP.red_sq h u hu r n j z)
      (HomP.r_sq h u hu (mm n) (hpt n) r j (x n)),
    (HomP.step (h.fW u hu r j) l e hz.2.symm (HomP.b_sq h u hu r j z) rfl).symm⟩

end CrystallineSemistableComparison.HT
