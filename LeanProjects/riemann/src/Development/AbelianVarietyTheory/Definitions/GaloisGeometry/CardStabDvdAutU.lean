import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SpKerColToEqColCpl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Aut

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def autU (N : Submodule (𝓞 E) (Sp E n)) : Subgroup (UF E n) where
  carrier := {γ | ∀ x, γ.1 x ∈ N ↔ x ∈ N}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b.1 x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹.1 x)
    rw [show a.1 (a⁻¹.1 x) = x from LinearEquiv.apply_symm_apply a.1 x] at h
    exact h.symm

theorem mem_autU {N : Submodule (𝓞 E) (Sp E n)} {γ : UF E n} : γ ∈ autU N ↔ gmap γ.1 N = N := by
  constructor
  · intro h
    ext x
    rw [mem_gmap, ← h (γ.1.symm x), LinearEquiv.apply_symm_apply]
  · intro h x
    conv_lhs => rw [← h, mem_gmap, LinearEquiv.symm_apply_apply]

end Aut

section Stab

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem card_dvd_card_autU (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q)
    (H : Subgroup (FrmG Λ Θ)) (hH : ∀ g ∈ H, g • p = p) : Nat.card H ∣ Nat.card (autU p.deco.1.N) := by
  let f : H →* autU p.deco.1.N :=
    { toFun := fun g => ⟨g.1.1, mem_autU.2 (congrArg (fun q : DecoF X.E n ST SG Q => q.deco.1.N) (hH g.1 g.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.card_dvd_of_injective f fun a b hab => ?_
  have h1 : a.1.1 = b.1.1 := congrArg Subtype.val hab
  have ha : FrmG.incl Λ Θ a.1 • p = p := hH a.1 a.2
  have hb : FrmG.incl Λ Θ b.1 • p = p := hH b.1 b.2
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1))
    (b := ((FrmG.incl Λ Θ b.1).1, (FrmG.incl Λ Θ b.1).2.1)) (congrArg DecoF.deco ha) (congrArg DecoF.deco hb) h1
  exact Subtype.ext (FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p ha hb h1 (Prod.mk.inj h2).2))

end Stab

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (Λ : LevFam X.E X.K (R.N R.m) Pr.vGs) (Θ : LevQFam X.E X.K (R.N R.m) (QE sel (mu : Chr X.F X.E X.K)))

@[reducible] def frmMem : MemOn (chF W sel mu L u R.m) where
  G := FrmG Λ Θ
  D := ChPt (R := R) sel mu u R.m
  actD := frmAct Λ Θ
  ρ := frmRho (colValF W sel mu u R.m) Λ Θ
  Nab := (colValF W sel mu u R.m).Nab
  Del := (colValF W sel mu u R.m).Del

theorem frmMem_gsd : (frmMem W sel mu L u Λ Θ).gsd = frmGSD (colValF W sel mu u R.m) Λ Θ := rfl

@[reducible] def cplMem : MemOn (chF W sel mu L u (m2 + 1)) :=
  MemOn.pairs (chF W sel mu L u (m2 + 1)) b (ybCpl W sel mu cst L u m2 b hY)

theorem cplMem_gsd : (cplMem W sel mu cst L u m2 b hY).gsd =
    cplGSD (midGSD W sel mu L u m2 b) (ybCpl W sel mu cst L u m2 b hY) := rfl

@[reducible] def levFam : ℕ → GFam X.K :=
  spFam (chF W sel mu L u) m2 R.m (cplMem W sel mu cst L u m2 b hY) (frmMem W sel mu L u Λ Θ)

variable {W sel mu cst L u m2 b hY Λ Θ}

def levPt : ∀ (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β),
    (levFam W sel mu cst L u m2 b hY Λ Θ i).D β → ChPt (R := R) sel mu u i
  | _, .mat _ _ => fun p => p
  | _, .cpl rfl => fun p => p.1.1
  | _, .top rfl => fun p => p

def levG : ∀ (i : ℕ) (_ : (levFam W sel mu cst L u m2 b hY Λ Θ i).β), LevFam X.E X.K (R.N i) Pr.vGs
  | i, .mat al _ => L.levG i al
  | _, .cpl rfl => L.levG (m2 + 1) b
  | _, .top rfl => Λ

def levQ : ∀ (i : ℕ) (_ : (levFam W sel mu cst L u m2 b hY Λ Θ i).β), LevQFam X.E X.K (R.N i) (QE sel (mu : Chr X.F X.E X.K))
  | i, .mat al _ => L.levQ i al
  | _, .cpl rfl => L.levQ (m2 + 1) b
  | _, .top rfl => Θ

def levGrp : ∀ (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β),
    (levFam W sel mu cst L u m2 b hY Λ Θ i).G β ≃* FrmG (levG i β) (levQ i β)
  | _, .mat _ _ => MulEquiv.refl _
  | _, .cpl rfl => MulEquiv.refl _
  | _, .top rfl => MulEquiv.refl _

theorem levPt_smul (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (g : (levFam W sel mu cst L u m2 b hY Λ Θ i).G β)
    (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) : levPt i β (g • d) = levGrp i β g • levPt i β d := by
  rcases β with _ | rfl | rfl <;> rfl

theorem levFam_rho (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (g : (levFam W sel mu cst L u m2 b hY Λ Θ i).G β) :
    (levFam W sel mu cst L u m2 b hY Λ Θ i).ρ β g = frmRho (colValF W sel mu u i) (levG i β) (levQ i β) (levGrp i β g) := by
  rcases β with _ | rfl | rfl <;> rfl

theorem levFam_nab (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) :
    (levFam W sel mu cst L u m2 b hY Λ Θ i).Nab β d = nabAtr X.emb (W.lamTrue u i) (levPt i β d).deco.1.Lsh := by
  rcases β with _ | rfl | rfl <;> rfl

theorem levFam_del (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) :
    (levFam W sel mu cst L u m2 b hY Λ Θ i).Del β d = delAtr X.emb (W.lamTrue u i) (levPt i β d).deco.1.Lsh := by
  rcases β with _ | rfl | rfl <;> rfl

theorem card_stab_dvd_autU (i : ℕ) (β : (levFam W sel mu cst L u m2 b hY Λ Θ i).β) (d : (levFam W sel mu cst L u m2 b hY Λ Θ i).D β) :
    Nat.card (MulAction.stabilizer ((levFam W sel mu cst L u m2 b hY Λ Θ i).G β) d) ∣ Nat.card (autU (levPt i β d).deco.1.N) := by
  have h := card_dvd_card_autU (levG i β) (levQ i β) (levPt i β d)
    ((MulAction.stabilizer ((levFam W sel mu cst L u m2 b hY Λ Θ i).G β) d).map (levGrp i β).toMonoidHom) (by
      rintro _ ⟨g, hg, rfl⟩
      exact (levPt_smul i β g d).symm.trans (congrArg (levPt i β) hg))
  rwa [Subgroup.card_map_of_injective (levGrp i β).injective] at h

theorem levFam_ok (hF : ∀ j, (chF W sel mu L u j).Ok) (hT : (frmGSD (colValF W sel mu u R.m) Λ Θ).Ok) (i : ℕ) :
    (levFam W sel mu cst L u m2 b hY Λ Θ i).Ok :=
  spFam_ok (fun j _ => hF j) (cplGSD_ok _ (hF (m2 + 1) b)) hT i

end Fam

end GlobalTheory.GO
