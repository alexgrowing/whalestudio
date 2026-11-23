import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjectsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectExtendOfPIsogenyDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ESValT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def scaleMap {S S' : Scheme.{0}} {s t : S ⟶ Sp R} {s' t' : S' ⟶ Sp R} {o : Obj b N s} {o₁ : Obj b N s'}
    {f : S' ⟶ S} (m : ObjMap o₁ o f) (e : ℕ) (h : s = t) (h' : s' = t') :
    ObjMap (ESDual.scale o₁ e h') (ESDual.scale o e h) f where
  φ := m.φ
  φ₂ := m.φ₂
  cart := m.cart
  sq := m.sq
  act := m.act
  pol := m.pol
  eta y := m.eta _

theorem extend_source : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ t₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ s₀ := by
  intro p _ D R _ _ _ _ b N hN hNp hpm r w j c _ _ _ _ _ M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst _ _ _ _ _ _ hψ _ V K _ _ _ _ _ _ y x hy
  set κ := spMap (algebraMap V K) with hκ
  obtain ⟨e, rfl⟩ := hψ.1
  obtain ⟨f', hf'⟩ := ESDual.exists_inv_exp (N := N) (by omega) hNp e
  obtain ⟨ψ', hψ'm, h₁, h₂⟩ := hψ.2.2.2.2.2
  haveI := hψ'm
  obtain ⟨hact, heta, ⟨hpol⟩⟩ := ESDual.dual_clauses hψ h₁ h₂
  have hrev : IsPIsog (p ^ e) (ESDual.scale o₀' f' rfl) o₀ ψ' := by
    refine ⟨⟨e, rfl⟩, hψ'm, hact, fun z => ?_, ⟨hpol⟩, ψ₀, hψ.2.1, h₂, h₁⟩
    show o₀.eta z = o₀'.eta (p ^ f' • z) ≫ ψ'
    rw [← heta, smul_smul, ← pow_add, ESDual.eta_congr o₀ hf' (pow_pos (Fact.out : p.Prime).pos _)]
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp K) (y ≫ M.s) κ oV
  have hb : κ ≫ y ≫ M.s = x ≫ s₀ ≫ M.s := by
    rw [← Category.assoc, hy, Category.assoc, ← hst]
  obtain ⟨o₁, ⟨m₁⟩⟩ : ∃ o₁ : Obj b N (κ ≫ y ≫ M.s), Nonempty (ObjMap o₁ o₀ x) := by
    rw [hb]; exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp K) (s₀ ≫ M.s) x o₀
  have mKU : ObjMap oK M.univ (x ≫ t₀) := hy ▸ ESDual.compMap mK mV
  obtain ⟨mK0, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ mKU mt₀
  obtain ⟨ψK, hψK, -⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N (p ^ e) Y₀ (Sp K) (s₀ ≫ M.s) (κ ≫ y ≫ M.s) x _ _
    (ESDual.scale oK f' rfl) o₁ (scaleMap mK0 f' rfl rfl) m₁ ψ' hrev
  obtain ⟨o'', ⟨m''⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_extend_of_pIsogeny_dvr p D R b N hN hNp (p ^ e) V K (y ≫ M.s) (ESDual.scale oV f' rfl)
    (ESDual.scale oK f' rfl) o₁ (scaleMap mK f' rfl rfl) ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o''
  refine ⟨z, ?_⟩
  obtain ⟨g, -, hg⟩ := M.rep (Sp K) (κ ≫ y ≫ M.s) o₁
  have e1 := hg (κ ≫ z) ⟨by rw [Category.assoc, hz], ⟨ESDual.compMap m'' mz⟩⟩
  have e2 := hg (x ≫ s₀) ⟨by rw [Category.assoc, hb], ⟨ESDual.compMap m₁ ms₀⟩⟩
  exact e1.trans e2.symm

end GlobalTheory.ESValT
