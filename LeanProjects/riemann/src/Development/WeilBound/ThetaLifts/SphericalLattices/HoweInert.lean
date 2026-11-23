import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology ValuativeRel GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

structure IsSph (om : Rep σ X W) (v : Pl F) (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) (s : Fn F n d v) : Prop where
  mem : s ∈ SB _
  gen : ∀ φ ∈ SB _, φ ∈ augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) s}
  line : ∀ φ ∈ SB _, ∃ (m : ℕ) (k : Fin (m + 1) → UA σ W.J) (w : Fin (m + 1) → ℂ) (c : ℂ),
    (∀ i, k i ∈ UAt σ W (evFin F v) ∧ w i • ω (1, k i) s = s) ∧ ∑ i, w i • ω (1, k i) φ - c • s ∈ augAt om v

def SphAt (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (v : Pl F) : Prop :=
  ∀ ω ρ, IsLocRep M ψ om v ω ρ → ∃ s, IsSph om v ω s

def IrrAt (om : Rep σ X W) (v : Pl F) : Prop := ∀ N, GlobalTheory.Published.ThetaSub om v N → N = augAt om v ∨ N = SB _

structure IsHowe (M : Model σ X W) (v : Pl F) (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) : Prop where
  fixX : ∀ g ∈ KAt σ X v, ω (g, 1) (M.vac v) = M.vac v
  fixW : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v
  genW : ∀ φ ∈ SB _, (∀ g ∈ KAt σ X v, ω (g, 1) φ = φ) →
    φ ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}
  genX : ∀ φ ∈ SB _, (∀ k ∈ KAt σ W v, ω (1, k) φ = φ) →
    φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}

structure IsVacSph (M : Model σ X W) (om : Rep σ X W) (v : Pl F) (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) : Prop where
  fixW : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v
  gen : ∀ φ ∈ SB _, φ ∈ augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}
  line : ∀ φ ∈ SB _, ∃ (m : ℕ) (k : Fin (m + 1) → UA σ W.J) (c : ℂ),
    (∀ i, k i ∈ KAt σ W v) ∧ ∑ i, ω (1, k i) φ - c • M.vac v ∈ augAt om v

structure IsSphForm (M : Model σ X W) (om : Rep σ X W) (v : Pl F) (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v))
    (l : Fn F n d v →ₗ[ℂ] ℂ) : Prop where
  aug : augAt om v ≤ LinearMap.ker l
  inv : ∀ k ∈ KAt σ W v, ∀ φ ∈ SB _, l (ω (1, k) φ) = l φ
  one : l (M.vac v) = 1

def AllTri (Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (_ : Base F E) (G : Geo σ a a') (_ : Rep σ G.V G.W) (_ : Rep σ G.V' G.W), Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, Q B G om om' v

def LatSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y, Φ ((g : GL (Fin n) k).1 * Y) = Φ Y) →
      Φ ∈ Submodule.span ℂ {f | ∃ h : GL (Fin d) k,
        f = fun Y => Set.indicator {Z : Matrix (Fin n) (Fin d) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) (Y * h.1)}

def SphSplit : Prop := AllTri fun {F E} _ _ _ _ _ {_ _ _} B G om om' v => Nonempty (E →ₐ[F] Fv F v) →
  (SphAt G.M B.ψ om v ∨ IrrAt om v) ∧ (SphAt G.M' B.ψ om' v ∨ IrrAt om' v)

def HoweInert : Prop := AllTri fun {F E} _ _ _ _ _ {_ _ _} B G om om' v => IsEmpty (E →ₐ[F] Fv F v) →
  (∀ ω ρ, IsLocRep G.M B.ψ om v ω ρ → IsHowe G.M v ω) ∧ ∀ ω ρ, IsLocRep G.M' B.ψ om' v ω ρ → IsHowe G.M' v ω

def VacInert : Prop := AllTri fun {F E} _ _ _ _ _ {_ _ _} B G om om' v => IsEmpty (E →ₐ[F] Fv F v) →
  (∀ ω ρ, IsLocRep G.M B.ψ om v ω ρ → IsVacSph G.M om v ω) ∧ ∀ ω ρ, IsLocRep G.M' B.ψ om' v ω ρ → IsVacSph G.M' om' v ω

def SphFun : Prop := AllTri fun {F E} _ _ _ _ _ {σ _ _} B G om om' v => IsEmpty (E →ₐ[F] Fv F v) →
  ∀ ω ρ ω' ρ', IsLocRep G.M B.ψ om v ω ρ → IsLocRep G.M' B.ψ om' v ω' ρ' →
    (∀ k ∈ KAt σ G.W v, ω (1, k) (G.M.vac v) = G.M.vac v) → (∀ k ∈ KAt σ G.W v, ω' (1, k) (G.M'.vac v) = G.M'.vac v) →
    ∃ l l', IsSphForm G.M om v ω l ∧ IsSphForm G.M' om' v ω' l' ∧
      ∀ h ∈ UAt σ G.W (evFin F v), l (ω (1, h) (G.M.vac v)) = l' (ω' (1, h) (G.M'.vac v))

def SphTri : Prop := AllTri fun B G om om' v =>
  (SphAt G.M B.ψ om v ∨ IrrAt om v) ∧ (SphAt G.M' B.ψ om' v ∨ IrrAt om' v)

theorem IsVacSph.isSph {M : Model σ X W} {om : Rep σ X W} {v : Pl F} {ω} (h : IsVacSph M om v ω) (hs : M.vac v ∈ SB _) :
    IsSph om v ω (M.vac v) :=
  ⟨hs, h.gen, fun φ hφ => by
    obtain ⟨m, k, c, h1, h2⟩ := h.line φ hφ
    exact ⟨m, k, fun _ => 1, c, fun i => ⟨(h1 i).1, by rw [one_smul, h.fixW _ (h1 i)]⟩, by simpa using h2⟩⟩

theorem sphTri_of (h1 : SphSplit) (h2 : VacInert) : SphTri := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v
  rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with he | he
  · obtain ⟨p, q⟩ := h2 F E σ B a a' G X om om' hT v he
    exact ⟨Or.inl fun ω ρ L => ⟨_, (p ω ρ L).isSph (hT.geo.hM.vac v).1⟩,
      Or.inl fun ω ρ L => ⟨_, (q ω ρ L).isSph (hT.geo.hM'.vac v).1⟩⟩
  · exact h1 F E σ B a a' G X om om' hT v he

end PositivityTheory.Sph

end
