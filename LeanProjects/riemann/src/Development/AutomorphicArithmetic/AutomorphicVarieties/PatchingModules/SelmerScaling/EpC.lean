import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

def _root_.UpperTheory.V.W.DD.map {X Y : Type} [CommRing X] [CommRing Y] {g : ℕ} (f : X →+* Y) : DD X g →+* DD Y g where
  toFun u := ⟨f u.a, fun j => f (u.ep j), fun j => f (u.ep' j), f u.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

def DD.aug (X : Type) [CommRing X] (g : ℕ) : DD X g →ₐ[X] X where
  toFun u := u.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n) {e : ℕ}

def epC (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (k : Fin e) (γ : G.G₀) : Matrix (Fin n) (Fin n) x.Fr :=
  (u γ).map (fun a => a.ep k) * x.ρX x.Fr (h.p₀ γ⁻¹)

def epC' (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (k : Fin e) (γ : G.G₀) : Matrix (Fin n) (Fin n) x.Fr :=
  (u γ).map (fun a => a.ep' k) * x.ρX x.Fr (h.p₀ γ⁻¹)

structure DefU (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ) : Prop where
  one : u 1 = 1
  mul : ∀ g g', u (g * g') = u g * u g'
  red : ∀ g, (u g).map (fun a => a.a) = x.ρX x.Fr (h.p₀ g)
  even : ∀ g, u g ∈ blkMat n x.a (ddPart x.A x.Fr e true false true false) (ddPart x.A x.Fr e false true false true)
  form : ∀ g, (u g)ᵀ * u (G.frame.conj g) =
    algebraMap x.A (DD x.Fr e) ((G.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD x.Fr e))
  ine : ∀ w, ∀ g ∈ G.frame.Iu w, u g = 1
  ψ_red : ∀ v i g, ((ψ v i g : (DD x.Fr e)ˣ) : DD x.Fr e).a = algebraMap x.A x.Fr (x.ψ v i g)
  ψ_even : ∀ v i g, ((ψ v i g : (DD x.Fr e)ˣ) : DD x.Fr e) ∈ ddPart x.A x.Fr e true false true false
  ψ_mu : ∀ v i, ∀ g ∈ G.frame.mu v, ψ v i g = 1
  ord : ∀ v (g : Fin n → L.Gv v), (List.ofFn fun i => u (G.φ v (g i)) -
    algebraMap (DD x.Fr e) (Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ v i (g i))).prod = 0
  bnd : BndD x.t u

end UpperTheory.V.Pa
