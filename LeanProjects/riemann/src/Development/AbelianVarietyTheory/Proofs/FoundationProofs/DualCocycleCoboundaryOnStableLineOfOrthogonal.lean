import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.OrdCob

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem matQ_one_zero (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (s : Dec (F := ℚ) B) :
    matQ c n W hint s 1 0 = 0 := by
  have h : (⟨mat W s 1 0, hint s 1 0⟩ : c.O) = 0 := Subtype.ext (hB s s.2)
  rw [matQ_apply, h, map_zero]

def rhoL (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) :
    Representation (ZMod (l ^ n)) (Dec (F := ℚ) B) (Qn c n) where
  toFun s := (AddMonoidHom.mulLeft (matQ c n W hint s 0 0)).toZModLinearMap (l ^ n)
  map_one' := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint 1 0 0 * x = x
    rw [matQ_one, Matrix.one_apply_eq, one_mul]
  map_mul' s t := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint ((s : G ℚ Ω) * (t : G ℚ Ω)) 0 0 * x =
      matQ c n W hint s 0 0 * (matQ c n W hint t 0 0 * x)
    rw [matQ_mul, Matrix.mul_apply, Fin.sum_univ_two, matQ_one_zero c n W hint B hB t, mul_zero, add_zero,
      mul_assoc]

theorem contAction_rhoL (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (hcont : Continuous W) :
    ReciprocityTheory.Gal.ContAction (rhoL c n W hint B hB) := by
  unfold ReciprocityTheory.Gal.ContAction
  rw [continuous_prod_of_discrete_right]
  intro x
  show Continuous fun s : Dec (F := ℚ) B => matQ c n W hint s 0 0 * x
  exact ((continuous_matQ_apply c n W hint hcont 0 0).comp continuous_subtype_val).mul continuous_const

theorem rhoS_single (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (s : Dec (F := ℚ) B) (u : Qn c n) :
    rhoS c n W hint S hN (locHom (S : Set Pl) B s) (Pi.single 0 u) =
      Pi.single 0 (rhoL c n W hint B hB s u) := by
  show matQ c n W hint s *ᵥ Pi.single 0 u = Pi.single 0 (matQ c n W hint s 0 0 * u)
  have h := matQ_one_zero c n W hint B hB s
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem dual_cob_on_line : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) (Mn c n), ∀ (s : Dec (F := ℚ) B) (u : Qn c n), f.1 s (Pi.single 0 u) = twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B s) m (Pi.single 0 u) - m (Pi.single 0 u) := by
  intro hL l _ Ω _ _ _ c n hn W hint hcont S hN μ hμ B v hBv hB f hf
  have hμχ : ∀ s : Dec (F := ℚ) B,
      μ (locHom (S : Set Pl) B s) = ((cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype) s := fun s =>
    DFunLike.congr_fun hμ (s : G ℚ Ω)
  have hinj := (hL.lt ℚ Ω l n (Qn c n) B (rhoL c n W hint B hB) v hn hBv
    (contAction_rhoL c n W hint B hB hcont)).2.2.1.1
  set χ : Dec (F := ℚ) B →* (ZMod (l ^ n))ˣ := (cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype with hχ
  have hs := rhoS_single c n W hint S hN B hB
  have hs' : ∀ (s : Dec (F := ℚ) B) (u : Qn c n),
      rhoS c n W hint S hN (locHom (S : Set Pl) B s)⁻¹ (Pi.single 0 u) =
        Pi.single 0 (rhoL c n W hint B hB s⁻¹ u) := fun s u => by rw [← map_inv, hs]
  let ι : Qn c n →ₗ[ZMod (l ^ n)] Mn c n := LinearMap.single (ZMod (l ^ n)) (fun _ : Fin 2 => Qn c n) 0
  let r : TDual (ZMod (l ^ n)) (Mn c n) → TDual (ZMod (l ^ n)) (Qn c n) := fun φ =>
    TDual.mk (LinearMap.comp (show Mn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) from φ) ι)
  have hψ : (fun s => r (f.1 s)) ∈ Z1 ((twDual χ (rhoL c n W hint B hB)).comp (MonoidHom.id _)) := by
    refine ⟨(continuous_of_discreteTopology (f := r)).comp f.2.1, fun g h => ?_⟩
    refine TDual.ext fun u => ?_
    have e : f.1 (g * h) (Pi.single 0 u) = f.1 g (Pi.single 0 u) +
        ((μ (locHom (S : Set Pl) B g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) *
          f.1 h (rhoS c n W hint S hN (locHom (S : Set Pl) B g)⁻¹ (Pi.single 0 u)) := by
      rw [f.2.2 g h]; rfl
    rw [hμχ, hs'] at e
    exact e
  have hcup : cupH1H1TwistedDual χ (rhoL c n W hint B hB) (MonoidHom.id _)
      ((contAction_rhoL c n W hint B hB hcont).comp' continuous_id) (Submodule.mkQ _ ⟨_, hψ⟩) = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a0, rfl⟩ := Submodule.mkQ_surjective _ x
    have ha : (fun s => ι (a0.1 s)) ∈ Z1 ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B)) := by
      refine ⟨(continuous_of_discreteTopology (f := ι)).comp a0.2.1, fun g h => ?_⟩
      show ι (a0.1 (g * h)) = ι (a0.1 g) +
        rhoS c n W hint S hN (locHom (S : Set Pl) B g) (Pi.single 0 (a0.1 h))
      rw [a0.2.2 g h, map_add, hs]
      rfl
    have hmem : Submodule.mkQ _ (⟨_, ha⟩ : Z1 _) ∈ ordCond c n W hint S hN B := by
      refine Submodule.mem_map.2 ⟨⟨_, ha⟩, (mem_ordZ _).2 ⟨0, fun s => ?_⟩, rfl⟩
      show (Pi.single 0 (a0.1 s) : Mn c n) 1 = _
      simp
    obtain ⟨cc, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (hf _ hmem))
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨cc, hcc, ?_⟩)
    funext p
    obtain ⟨g, h⟩ := p
    have e : ((μ (locHom (S : Set Pl) B g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * cc h - cc (g * h) + cc g =
        f.1 g (rhoS c n W hint S hN (locHom (S : Set Pl) B g) (Pi.single 0 (a0.1 h))) := congrFun hd (g, h)
    rw [hμχ, hs] at e
    exact e
  have h0 := hinj (hcup.trans (map_zero _).symm)
  obtain ⟨m0, hm0⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
  refine ⟨TDual.mk (LinearMap.comp (show Qn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) from m0) (LinearMap.proj 0)),
    fun s u => ?_⟩
  have e : f.1 s (Pi.single 0 u) =
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * m0 (rhoL c n W hint B hB s⁻¹ u) - m0 u :=
    congrArg (fun φ : TDual (ZMod (l ^ n)) (Qn c n) => φ u) (hm0 s)
  rw [e, twDual_apply, hμχ, hs']
  rfl

end GlobalTheory.Ord2.OrdCob
