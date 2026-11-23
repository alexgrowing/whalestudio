import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc.Ptransl

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def trH (c : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun p := (p.1 - c, p.2)
  invFun p := (p.1 + c, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.sub continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.add continuous_const).prodMk continuous_snd

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem comp_mem {U V : Set (Sp k n)} (e : Sp k n ≃ₜ Sp k n) (hUV : ∀ p, e p ∈ U → p ∈ V) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn U) : (fun p => f (e p)) ∈ supportedIn V := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
  intro p hp
  exact hUV p (hsupp hp)

theorem act_trH {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    {g : GL (Fin n) k} (hg : g ∈ Gz Z) (p : Sp k n) : act g (trH c p) = trH c (act g p) := by
  have hcomm : c * (g : Matrix (Fin n) (Fin n) k) = g * c := hg c hc
  have hconj : (g : Matrix (Fin n) (Fin n) k) * c * (g⁻¹ : GL (Fin n) k) = c := by
    rw [← hcomm, Matrix.mul_assoc]
    simp
  simp only [act, trH, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Prod.mk.injEq, and_true]
  rw [Matrix.mul_sub, Matrix.sub_mul, hconj]

theorem transl : Transl k := by
  intro m Z hCR hNB c hc F hF hnil ξ hsupp hinv
  let ξ' : (Sp k m → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (trH c))
  have hξ' : ∀ f, ξ' f = ξ (fun p => f (trH c p)) := fun f => rfl
  have hmem : ∀ f ∈ supportedIn (Set.univ : Set (Sp k m)),
      (fun p => f (trH c p)) ∈ supportedIn (Set.univ : Set (Sp k m)) :=
    fun f hf => comp_mem (trH c) (fun _ _ => Set.mem_univ _) hf
  have hS : Supp ξ' (NB Z ×ˢ Set.univ) := by
    intro f hf hz
    rw [hξ']
    refine hsupp _ (hmem f hf) ?_
    rintro ⟨x, v⟩ ⟨hx, -⟩
    apply hz
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · intro a ha
      have h1 : a * x = x * a := hF hx a ha
      have h2 : a * c = c * a := hCR.1 a ha c hc
      change a * (x - c) = (x - c) * a
      rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]
    · exact hnil x hx
  have hI : T.Inv Z ξ' := by
    intro g hg f hf
    rw [hξ', hξ']
    have : (fun p => f (act g (trH c p))) = (fun p => (fun q => f (trH c q)) (act g p)) := by
      funext p
      rw [act_trH hc hg]
    rw [this]
    exact hinv g hg _ (hmem f hf)
  have hK := hNB ξ' hS hI
  intro f hf
  have hf' : (fun p => f ((trH c).symm p)) ∈ supportedIn {p : Sp k m | p.2 ≠ 0} :=
    comp_mem (trH c).symm (fun _ h => h) hf
  have := hK _ hf'
  rw [hξ'] at this
  simpa using this

end PositivityTheory.RgUd.TP.Loc.Ptransl
